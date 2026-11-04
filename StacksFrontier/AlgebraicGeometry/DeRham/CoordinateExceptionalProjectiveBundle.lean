module

public import StacksFrontier.AlgebraicGeometry.Conormal.FreeOfCotangentBasis
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalBundle
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism
public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.BaseChange

/-!
# The exceptional divisor of the standard coordinate blowup is `𝐏^{n-1}_Z`

Fix a ring `R` and integers `m ≥ 0`, `n ≥ 1`. Let `Z = 𝐀^m_R ⟶ 𝐀^{m+n}_R = X` be the coordinate
closed immersion and let `E` be the exceptional divisor of the blowing up `L ⟶ X` along `Z`.
Section 50.16 of the source ([Stacks, Tag 0FUB]) identifies `E` with `P = 𝐏^{n-1}_Z`.  This file
proves that identification, over the centre.

The proof composes four isomorphisms over the centre:

1. `E ≅ 𝐏(𝒞_{Z/X})`, the projective bundle of the conormal sheaf ([Stacks, Tag 0FUT],
   `Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle`);
2. `𝒞_{Z/X} ≅ 𝒪_Z^n`, with basis the classes of the last `n` coordinates
   (`Stacks.DeRham.CoordinateExceptional.coordinateConormalFreeIso`), hence
   `𝐏(𝒞_{Z/X}) ≅ 𝐏(𝒪_Z^n)`;
3. `𝐏(𝒪_Z^n) ≅ 𝐏^{n-1}_Z` ([Stacks, Tag 01OE],
   `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`), read through the comparison of the two
   presentations of the projective bundle;
4. the closed subscheme `V(I)` cut out by the coordinate ideal is the centre `Z` itself.

The algebraic input of step 2 is that `Σ cⱼ yⱼ ∈ I²` forces every `cⱼ ∈ I`, for
`I = (y₁, …, yₙ) ⊆ R[x, y]`.  This is proved by differentiating in `yⱼ`.

## Main definitions

* `Stacks.DeRham.CoordinateExceptional.coordinateConormalFreeIso`: `𝒪_{V(I)}^n ≅ 𝒞_{V(I)/X}`.
* `Stacks.DeRham.coordinateExceptionalIsoBundle`: **`E ≅ 𝐏^{n-1}_Z`**, for `n = k + 1`.

## Main results

* `Stacks.DeRham.coordinateExceptionalIsoBundle_hom_toCentre`: the identification is over the
  centre.  It carries the projection `p : P ⟶ Z` to the projection
  `Stacks.DeRham.coordinateExceptionalToCentre` of the exceptional divisor.

## Implementation notes

The rank is written `k + 1` rather than `n` with `1 ≤ n`.  Then the bundle is
`𝐏^{k+1-1}_Z = 𝐏^k_Z` definitionally, and the free module of rank `k + 1` is the one of
[Stacks, Tag 01OE] on the nose.  No `@[stacks]` attribute is attached: the identification is part
of the standing situation of the source's Section 50.16, not a numbered statement.

## References

* [Stacks Project, Tag 0FUB](https://stacks.math.columbia.edu/tag/0FUB)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The partial derivative in a last coordinate carries the square of the coordinate ideal into
the coordinate ideal. -/
theorem pderiv_mem_coordinateRingIdeal_of_mem_sq (j : Fin n) {p : MvPolynomial (Fin m ⊕ Fin n) R}
    (hp : p ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ 2) :
    pderiv (Sum.inr j) p ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [pderiv_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
  · rw [map_add]; exact Ideal.add_mem _ ha hb

/-- **The last coordinates are linearly independent modulo the square of the coordinate ideal:**
if `Σ cₖ yₖ ∈ I²` then every `cⱼ ∈ I`. -/
theorem mem_coordinateRingIdeal_of_sum_mem_sq (c : Fin n → MvPolynomial (Fin m ⊕ Fin n) R)
    (h : (∑ k, c k * X (Sum.inr k)) ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ 2)
    (j : Fin n) : c j ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n := by
  classical
  have hd := pderiv_mem_coordinateRingIdeal_of_mem_sq R m n j h
  rw [map_sum] at hd
  have hsplit : ∑ k, pderiv (Sum.inr j) (c k * X (Sum.inr k)) =
      (∑ k, pderiv (Sum.inr j) (c k) * X (Sum.inr k)) + c j := by
    simp only [pderiv_mul, pderiv_X, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, Sum.inr.injEq]
  rw [hsplit] at hd
  have hmem : (∑ k, pderiv (Sum.inr j) (c k) * X (Sum.inr k)) ∈
      Stacks.MoreMorphisms.coordinateRingIdeal R m n :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
      (Stacks.MoreMorphisms.X_inr_mem_coordinateRingIdeal R m n k)
  simpa using (Ideal.add_mem_iff_right _ hmem).1 hd

namespace CoordinateExceptional

open Stacks.MoreMorphisms

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

/-- The closed immersion of the closed subscheme cut out by the coordinate ideal. -/
abbrev coordinateSubschemeι :
    (coordinateIdeal R m n).subscheme ⟶ Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)) :=
  (coordinateIdeal R m n).subschemeι

/-- On global sections, the kernel of the closed immersion of `V(I)` is the coordinate ideal. -/
theorem chartIdeal_coordinateSubschemeι :
    Stacks.Conormal.chartIdeal (coordinateSubschemeι R m n)
        (Stacks.Blowup.AffineModel.wholeSpace _) =
      (coordinateRingIdeal R m n).map (gammaEquiv R m n : _ →+* _) :=
  ((coordinateIdeal R m n).ker_subschemeι_app (topAffineOpen R m n)).trans
    (coordinateIdeal_ideal_top R m n)

/-- The `j`-th of the last `n` coordinates, as a global section of the kernel ideal of the
closed immersion of the centre. -/
def coordinateChartIdealSection (j : Fin n) :
    Stacks.Conormal.chartIdeal (coordinateSubschemeι R m n)
        (Stacks.Blowup.AffineModel.wholeSpace _) :=
  ⟨coordinateSection R m n j, by
    rw [chartIdeal_coordinateSubschemeι]
    exact Ideal.mem_map_of_mem _ (X_inr_mem_coordinateRingIdeal R m n j)⟩

/-- The coercion of `coordinateChartIdealSection` is the coordinate section. -/
private theorem coe_coordinateChartIdealSection (j : Fin n) :
    (coordinateChartIdealSection R m n j :
      Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)) = coordinateSection R m n j :=
  rfl

/-- The last coordinates generate the kernel ideal. -/
theorem chartIdeal_le_span_coordinateChartIdealSection :
    Stacks.Conormal.chartIdeal (coordinateSubschemeι R m n)
        (Stacks.Blowup.AffineModel.wholeSpace _) ≤
      Ideal.span (Set.range fun j => (coordinateChartIdealSection R m n j :
        Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤))) := by
  simp only [coe_coordinateChartIdealSection]
  rw [chartIdeal_coordinateSubschemeι, coordinateRingIdeal, Ideal.map_span,
    ← Set.range_comp]
  rfl

/-- `mem_coordinateRingIdeal_of_sum_mem_sq`, read on global sections of `𝐀^{m+n}_R`. -/
theorem mem_chartIdeal_of_sum_mem_sq
    (c : Fin n → Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤))
    (h : (∑ j, c j * (coordinateChartIdealSection R m n j :
        Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤))) ∈
      Stacks.Conormal.chartIdeal (coordinateSubschemeι R m n)
          (Stacks.Blowup.AffineModel.wholeSpace _) ^ 2)
    (j : Fin n) :
    c j ∈
      Stacks.Conormal.chartIdeal (coordinateSubschemeι R m n)
          (Stacks.Blowup.AffineModel.wholeSpace _) := by
  simp only [coe_coordinateChartIdealSection] at h
  rw [chartIdeal_coordinateSubschemeι] at h ⊢
  rw [← Ideal.map_pow] at h
  have h' := (Ideal.mem_map_of_equiv (gammaEquiv R m n) _).1 h
  obtain ⟨p, hp, hpe⟩ := h'
  have hpsum : p = ∑ k, (gammaEquiv R m n).symm (c k) * X (Sum.inr k) := by
    apply (gammaEquiv R m n).injective
    rw [hpe, map_sum]
    simp [coordinateSection]
  rw [hpsum] at hp
  have := mem_coordinateRingIdeal_of_sum_mem_sq R m n _ hp j
  have hcj : c j = (gammaEquiv R m n) ((gammaEquiv R m n).symm (c j)) := by simp
  rw [hcj]
  exact Ideal.mem_map_of_mem _ this

/-- **The conormal sheaf of the coordinate centre is free of rank `n`**, with basis the classes of
the last `n` coordinates. -/
def coordinateConormalFreeIso :
    Scheme.Modules.free (coordinateIdeal R m n).subscheme (ULift.{u} (Fin n)) ≅
      Stacks.Conormal.conormalModule (coordinateSubschemeι R m n) :=
  haveI := Stacks.Conormal.isIso_conormalFreeHom (coordinateSubschemeι R m n)
    (coordinateChartIdealSection R m n) (chartIdeal_le_span_coordinateChartIdealSection R m n)
    (mem_chartIdeal_of_sum_mem_sq R m n)
  asIso (Stacks.Conormal.conormalFreeHom (coordinateSubschemeι R m n)
    (coordinateChartIdealSection R m n))

/-- The closed subscheme cut out by the coordinate ideal is the centre. -/
theorem isIso_centreFromSubscheme : IsIso (centreFromSubscheme R m n) :=
  IsClosedImmersion.isIso_lift _ _ (ker_coordinateEmbedding_eq R m n)

/-- Affine `(m + n)`-space is smooth over its base. -/
instance smooth_coordinateAmbientToBase : Smooth (coordinateAmbientToBase R m n) :=
  smooth_specMap _ (smooth_mvPolynomial_C R _)

/-- The closed subscheme cut out by the coordinate ideal is smooth over the base. -/
instance smooth_coordinateSubschemeι_comp :
    Smooth (coordinateSubschemeι R m n ≫ coordinateAmbientToBase R m n) := by
  have : IsIso (centreFromSubscheme R m n) := isIso_centreFromSubscheme R m n
  have h : coordinateSubschemeι R m n ≫ coordinateAmbientToBase R m n =
      centreFromSubscheme R m n ≫ coordinateBlowupCentreToBase R m := by
    rw [← centreFromSubscheme_comp_coordinateEmbedding_assoc]
    congr 1
    rw [Stacks.MoreMorphisms.coordinateEmbedding, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => by simp [Stacks.MoreMorphisms.coordinateProjection]
  rw [h]
  have : Smooth (coordinateBlowupCentreToBase R m) :=
    smooth_specMap _ (smooth_mvPolynomial_C R _)
  infer_instance

variable (k : ℕ)

/-- The free module of rank `k + 1` on the centre subscheme, identified with the conormal sheaf
read as the inverse image of itself along the identity. -/
def conormalFreePullbackIso :
    Stacks.SymGraded.freeModule (X := (coordinateIdeal R m (k + 1)).subscheme)
        (Stacks.SymGraded.coordIndex.{u} k) ≅
      (Scheme.Modules.pullback (𝟙 _)).obj
        (Stacks.Conormal.conormalModule (coordinateSubschemeι R m (k + 1))) :=
  coordinateConormalFreeIso R m (k + 1) ≪≫ (Scheme.Modules.pullbackId _).symm.app _

/-- `𝐏(𝒪^{k+1}) ≅ 𝐏(𝒞)` over the centre subscheme. -/
def bundleFreeIsoConormal :
    Stacks.RelativeProj.projectiveBundle (coordinateIdeal R m (k + 1)).subscheme
        (Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex.{u} k)) ≅
      Stacks.RelativeProj.projectiveBundle (coordinateIdeal R m (k + 1)).subscheme
        (Stacks.Conormal.conormalModule (coordinateSubschemeι R m (k + 1))) :=
  have := (Stacks.RelativeProj.isPullback_projectiveBundleBaseChange (𝟙 _) _ _
    (conormalFreePullbackIso R m k)).isIso_fst_of_isIso
  asIso (Stacks.RelativeProj.projectiveBundleBaseChange (𝟙 _) _ _ (conormalFreePullbackIso R m k))

/-- `bundleFreeIsoConormal` is an isomorphism over the centre subscheme. -/
theorem bundleFreeIsoConormal_hom_toBase :
    (bundleFreeIsoConormal R m k).hom ≫ Stacks.RelativeProj.projectiveBundleToBase _ _ =
      Stacks.RelativeProj.projectiveBundleToBase _ _ := by
  have := (Stacks.RelativeProj.isPullback_projectiveBundleBaseChange (𝟙 _) _ _
    (conormalFreePullbackIso R m k)).w
  simpa [bundleFreeIsoConormal] using this

/-- `𝐏(𝒪^{k+1}) ≅ ℙ^k` over the centre subscheme: the two presentations of the projective bundle
followed by [Stacks, Tag 01OE]. -/
def bundleFreeIsoProjectiveSpace :
    Stacks.RelativeProj.projectiveBundle (coordinateIdeal R m (k + 1)).subscheme
        (Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex.{u} k)) ≅
      projectiveSpaceOver k (coordinateIdeal R m (k + 1)).subscheme :=
  (Stacks.RelativeProj.bundlePresentationIso _).symm ≪≫
    Stacks.SymGraded.projectiveBundleIsoProjectiveSpace k

/-- `bundleFreeIsoProjectiveSpace` is an isomorphism over the centre subscheme. -/
@[reassoc]
theorem bundleFreeIsoProjectiveSpace_hom_fst :
    (bundleFreeIsoProjectiveSpace R m k).hom ≫ pullback.fst _ _ =
      Stacks.RelativeProj.projectiveBundleToBase _ _ := by
  rw [bundleFreeIsoProjectiveSpace, Iso.trans_hom, Category.assoc,
    Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst, Iso.symm_hom]
  exact Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase _

/-- Projective space over the centre subscheme is projective space over the centre. -/
def projectiveSpaceSubschemeIso :
    projectiveSpaceOver k (coordinateIdeal R m (k + 1)).subscheme ≅
      projectiveSpaceOver k (coordinateBlowupCentre R m) :=
  have : IsIso (centreFromSubscheme R m (k + 1)) := isIso_centreFromSubscheme R m (k + 1)
  have := (Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.isPullback_map k
    (centreFromSubscheme R m (k + 1))).isIso_snd_of_isIso
  asIso (Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.map k (centreFromSubscheme R m (k + 1)))

/-- `projectiveSpaceSubschemeIso` lies over the identification of `V(I)` with the centre. -/
theorem projectiveSpaceSubschemeIso_hom_fst :
    (projectiveSpaceSubschemeIso R m k).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ centreFromSubscheme R m (k + 1) :=
  Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.map_fst k _

end CoordinateExceptional

open CoordinateExceptional in
/-- **The exceptional divisor of the standard coordinate blowup is `𝐏^{n-1}_Z`.** -/
def coordinateExceptionalIsoBundle (k : ℕ) :
    coordinateExceptionalScheme R m (k + 1) ≅ coordinateBlowupBundle R m (k + 1) :=
  Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle
      (coordinateAmbientToBase R m (k + 1)) (Stacks.MoreMorphisms.coordinateIdeal R m (k + 1)) ≪≫
    (bundleFreeIsoConormal R m k).symm ≪≫ bundleFreeIsoProjectiveSpace R m k ≪≫
    projectiveSpaceSubschemeIso R m k

open CoordinateExceptional in
/-- **The identification `E ≅ 𝐏^{n-1}_Z` is an identification over the centre.** -/
theorem coordinateExceptionalIsoBundle_hom_toCentre (k : ℕ) :
    (coordinateExceptionalIsoBundle R m k).hom ≫ coordinateBlowupBundleToCentre R m (k + 1) =
      coordinateExceptionalToCentre R m (k + 1) := by
  have h1 := Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle_hom_toCentre
    (coordinateAmbientToBase R m (k + 1)) (Stacks.MoreMorphisms.coordinateIdeal R m (k + 1))
  have h2 : (bundleFreeIsoConormal R m k).inv ≫ Stacks.RelativeProj.projectiveBundleToBase _ _ =
      Stacks.RelativeProj.projectiveBundleToBase _ _ := by
    rw [Iso.inv_comp_eq, bundleFreeIsoConormal_hom_toBase]
  show (coordinateExceptionalIsoBundle R m k).hom ≫ pullback.fst (terminal.from _)
    (terminal.from (projectiveSpaceAtUniverse.{u} k)) = _
  rw [coordinateExceptionalIsoBundle, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Category.assoc, Category.assoc,
    projectiveSpaceSubschemeIso_hom_fst, bundleFreeIsoProjectiveSpace_hom_fst_assoc,
    reassoc_of% h2, reassoc_of% h1, coordinateExceptionalToCentre,
    Scheme.IdealSheafData.comapIso_hom_snd_assoc]

end Stacks.DeRham
