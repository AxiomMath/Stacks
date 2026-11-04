module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecTruncation
public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalizationPunctured

/-!
# The cone is the base, away from the vertex

Let `A = ⨁_{d ≥ 0} A_d` be a nonnegatively graded ring, `X = Spec A`, `U = X ∖ V(A₊)` and let
`L = Proj B` be the cone over `P = Proj A` attached to the truncation algebra
`B = ⨁_{d ≥ 0} A_{≥ d}`, with structure morphism `L ⟶ X`. **That morphism restricts to an
isomorphism over `U`**, which is the equality on the left of the diagram of [Stacks, Tag 0EKG].

Over the standard open `D(f)` of a homogeneous `f` of positive degree the statement is
algebraic. The part of `L` lying over `D(f)` is the standard open `D₊(σ f · ψ f)`, whose
functions are the degree-zero part `(B[1/σ f · ψ f])₀` of a localization of `B`, and the ring
map `A ⟶ (B[1/σ f · ψ f])₀` induced by the structure morphism inverts `f`: the inverse of
`σ f` is `ψ f / (σ f · ψ f)`. The resulting map `A[1/f] ⟶ (B[1/σ f · ψ f])₀` is an isomorphism,
because composing it with the comparison isomorphism
`Stacks.Truncation.puncturedRingEquiv` of [Stacks, Tag 0EKG] gives a ring map `A[1/f] ⟶ A[1/f]`
over `A`, hence the identity. Geometrically this says that `L ⟶ X` identifies `D₊(σ f · ψ f)`
with `D(f)`, and the standard opens of the positive-degree homogeneous elements cover `U`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.awayHom`: the ring map
  `A ⟶ (B[1/σ f · ψ f])₀` through which `L ⟶ X` acts on functions over `D(f)`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.awayLocHom`: its factorization
  `A[1/f] ⟶ (B[1/σ f · ψ f])₀`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.bijective_awayLocHom`: **`A[1/f]` is the ring
  of functions on the part of `L` lying over `D(f)`**.
* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.awayι_comp_toSpecA`: on the chart
  `Spec (B[1/σ f · ψ f])₀` of `L` the structure morphism is `Spec` of that ring map.
* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.isIso_toSpecA_restrict_specBasicOpen`:
  **`L ⟶ X` is an isomorphism over `D(f)`**.
* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.isIso_toSpecA_restrict`: **`L ⟶ X` is an
  isomorphism over `U`**.

## Implementation notes

The inverse of the image of `σ f` is written with `HomogeneousLocalization.Away.mk`, whose
numerator must be homogeneous of degree `n • d` for the `n`-th power of the denominator; with
`n = 1` the numerator is `ψ f`, of degree `d`.

That the map on functions is an isomorphism is not computed from a description of the inverse:
`Stacks.Truncation.puncturedToLocalization` is already known to be bijective, and the composite
of the two is a ring map `A[1/f] ⟶ A[1/f]` commuting with `A ⟶ A[1/f]`, hence the identity by
the universal property of the localization. A left inverse of a bijection is its inverse.

The two charts of the restricted morphism — `Spec (B[1/σ f · ψ f])₀ ⟶ L` on the source and
`Spec A[1/f] ⟶ X` on the target — are open immersions with the right images, so
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` identifies them with the two opens, and the
square they form with the structure morphism exhibits the restriction as an isomorphism
conjugated by two isomorphisms. Over `U` the statement follows because being an isomorphism
over an open is local on that open, and the standard opens of the positive-degree homogeneous
elements cover `U`; they are indexed here by pairs `(k, f)` with `f ∈ A_{k+1}`, so that the
positivity of the degree is built into the index.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjAndSpecTruncation

universe u

section IsoOverU

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {f : A}

/-! ### The functions on the part of `L` lying over a standard open of `X` -/

/-- **The ring map `A ⟶ (B[1/σ f · ψ f])₀`** through which the structure morphism `L ⟶ X` acts
on functions over the standard open `D(f)`: the identification `σ : A ≃ B₀` followed by the
inclusion of `B₀` in the degree-zero part of the localization of `B` at `σ f · ψ f`. -/
def awayHom (f : A) : A →+* HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) :=
  (HomogeneousLocalization.fromZeroRingHom (grading 𝒜)
    (Submonoid.powers (sigmaMulPsi 𝒜 f))).comp (sigma 𝒜).toRingHom

/-- The value of `awayHom 𝒜 f a` in the localization of `B` is the fraction `σ a / 1`. -/
theorem val_awayHom (a : A) :
    (awayHom 𝒜 f a).val =
      Localization.mk ((sigma 𝒜 a : grading 𝒜 0) : TruncationRing 𝒜) 1 :=
  rfl

/-- The fraction `ψ f / (σ f · ψ f)`, which inverts the image of `σ f`. -/
def awayInvSigma (hf : f ∈ 𝒜 d) :
    HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) :=
  HomogeneousLocalization.Away.mk (grading 𝒜) (sigmaMulPsi_mem_grading 𝒜 d hf) 1 (psi 𝒜 f)
    (by simpa using (psi 𝒜).map_mem hf)

/-- **The image of `f` in `(B[1/σ f · ψ f])₀` is a unit**, with inverse `ψ f / (σ f · ψ f)`:
the product of the two is `(σ f · ψ f) / (σ f · ψ f)`. -/
theorem isUnit_awayHom_self (hf : f ∈ 𝒜 d) : IsUnit (awayHom 𝒜 f f) := by
  refine isUnit_iff_exists_inv.mpr ⟨awayInvSigma 𝒜 d hf, ?_⟩
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mul, val_awayHom, awayInvSigma,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
    Localization.mk_mul]
  refine Eq.trans (congrArg₂ Localization.mk ?_ (Subtype.ext ?_))
    (Localization.mk_self (⟨sigmaMulPsi 𝒜 f, 1, pow_one _⟩ : Submonoid.powers _))
  · rfl
  · simp

/-- **The factorization `A[1/f] ⟶ (B[1/σ f · ψ f])₀`** of the map on functions. -/
def awayLocHom (hf : f ∈ 𝒜 d) :
    Localization.Away f →+* HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f) :=
  IsLocalization.Away.lift f (g := awayHom 𝒜 f) (isUnit_awayHom_self 𝒜 d hf)

/-- `awayLocHom` factors `awayHom` through the localization map `A ⟶ A[1/f]`. -/
theorem awayLocHom_comp (hf : f ∈ 𝒜 d) :
    (awayLocHom 𝒜 d hf).comp (algebraMap A (Localization.Away f)) = awayHom 𝒜 f :=
  IsLocalization.Away.lift_comp f (isUnit_awayHom_self 𝒜 d hf)

/-- **The comparison map undoes `A ⟶ (B[1/σ f · ψ f])₀`**: the image of `a` is the fraction
`a⁽⁰⁾ / 1`, which the comparison sends to `a / 1`. -/
theorem puncturedToLocalization_awayHom (hf : f ∈ 𝒜 d) (a : A) :
    puncturedToLocalization 𝒜 (awayHom 𝒜 f a) = algebraMap A (Localization.Away f) a := by
  have hmem : a ∈ truncation 𝒜 (0 * d) := by
    rw [Nat.zero_mul]
    exact mem_truncation_zero 𝒜 a
  have hval : awayHom 𝒜 f a = puncturedElt 𝒜 d hf 0 a hmem := by
    refine HomogeneousLocalization.val_injective _ ?_
    rw [val_awayHom, puncturedElt, HomogeneousLocalization.val_mk]
    refine congrArg₂ Localization.mk ?_ (Subtype.ext ?_)
    · rw [coe_sigma_eq_degElt]
      exact degElt_congr 𝒜 (Nat.zero_mul d).symm rfl _ _
    · simp
  rw [hval, puncturedToLocalization_puncturedElt 𝒜 d hf 0 a hmem, Nat.mul_zero,
    awayFrac_zero_eq_algebraMap]

/-- The comparison map is a left inverse of `A[1/f] ⟶ (B[1/σ f · ψ f])₀`: both composites with
`A ⟶ A[1/f]` are that map, so the universal property of the localization identifies them. -/
theorem puncturedToLocalization_comp_awayLocHom (hf : f ∈ 𝒜 d) :
    (puncturedToLocalization 𝒜).comp (awayLocHom 𝒜 d hf) =
      RingHom.id (Localization.Away f) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => ?_)
  rw [RingHom.comp_assoc, awayLocHom_comp 𝒜 d hf]
  simpa using puncturedToLocalization_awayHom 𝒜 d hf a

/-- **`A[1/f]` is the ring of functions on the part of `L` lying over `D(f)`.** The comparison
map is bijective and is a left inverse of the map in question, which is therefore its
inverse. -/
theorem bijective_awayLocHom (hf : f ∈ 𝒜 d) : Function.Bijective (awayLocHom 𝒜 d hf) := by
  have hleft : ∀ z, puncturedToLocalization 𝒜 (awayLocHom 𝒜 d hf z) = z := fun z =>
    congrFun (congrArg (fun φ : Localization.Away f →+* Localization.Away f =>
      (φ : Localization.Away f → Localization.Away f))
      (puncturedToLocalization_comp_awayLocHom 𝒜 d hf)) z
  refine ⟨Function.LeftInverse.injective hleft, fun y => ?_⟩
  exact ⟨puncturedToLocalization 𝒜 y,
    puncturedToLocalization_injective 𝒜 d hf (hleft _)⟩

/-! ### The structure morphism over a standard open of `X` -/

/-- **On the chart `Spec (B[1/σ f · ψ f])₀` of `L` the structure morphism `L ⟶ X` is `Spec` of
the map on functions**, factored through `A[1/f]`. -/
theorem awayι_comp_toSpecA (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι (grading 𝒜) (sigmaMulPsi 𝒜 f) (sigmaMulPsi_mem_grading 𝒜 d hf) hd ≫
        toSpecA 𝒜 =
      Spec.map (CommRingCat.ofHom (awayLocHom 𝒜 d hf)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) := by
  rw [toSpecA, ProjAndSpec.toSpecA, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    awayLocHom_comp 𝒜 d hf]
  rfl

/-- An open immersion with range an open `U` is an isomorphism onto `U` compatible with `U.ι`. -/
private theorem exists_iso_comp_ι {X Y : Scheme} (g : X ⟶ Y) [IsOpenImmersion g] (U : Y.Opens)
    (h : g.opensRange = U) : ∃ e : X ≅ U, e.hom ≫ U.ι = g :=
  have hset : Set.range g.base = Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, ← h]
    rfl
  ⟨IsOpenImmersion.isoOfRangeEq g U.ι hset, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hset⟩

/-- **The structure morphism `L ⟶ X` is an isomorphism over a standard open `D(f)`** of a
homogeneous element of positive degree. -/
theorem isIso_toSpecA_restrict_specBasicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    IsIso (toSpecA 𝒜 ∣_ ProjAndSpec.specBasicOpen f) := by
  have hg : sigmaMulPsi 𝒜 f ∈ grading 𝒜 d := sigmaMulPsi_mem_grading 𝒜 d hf
  have hiso : IsIso (CommRingCat.ofHom (awayLocHom 𝒜 d hf)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_awayLocHom 𝒜 d hf)
  obtain ⟨e, hfac⟩ := exists_iso_comp_ι (Proj.awayι (grading 𝒜) (sigmaMulPsi 𝒜 f) hg hd)
    (toSpecA 𝒜 ⁻¹ᵁ ProjAndSpec.specBasicOpen f) <| by
      rw [Proj.opensRange_awayι]
      exact (toSpecA_preimage_specBasicOpen 𝒜 f d hf).symm
  obtain ⟨e', hfac'⟩ := exists_iso_comp_ι
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
    (ProjAndSpec.specBasicOpen f) <| by
      refine TopologicalSpace.Opens.ext ?_
      rw [Scheme.Hom.coe_opensRange]
      exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have key : e.hom ≫ (toSpecA 𝒜 ∣_ ProjAndSpec.specBasicOpen f) =
      Spec.map (CommRingCat.ofHom (awayLocHom 𝒜 d hf)) ≫ e'.hom := by
    rw [← cancel_mono (ProjAndSpec.specBasicOpen f).ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, hfac, awayι_comp_toSpecA 𝒜 d hf hd,
      hfac']
  have hcomp : IsIso (e.hom ≫ (toSpecA 𝒜 ∣_ ProjAndSpec.specBasicOpen f)) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

/-! ### The structure morphism over `U` -/

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The open `U = X ∖ V(A₊)` is the union of the standard opens of the homogeneous elements of
degree `k + 1`, indexed by the pairs `(k, f)`. -/
theorem openU_eq_iSup_sigma :
    ProjAndSpec.openU 𝒜 =
      ⨆ i : (k : ℕ) × ↥(𝒜 (k + 1)), ProjAndSpec.specBasicOpen ((i.2 : A)) := by
  refine le_antisymm (iSup_le fun e => iSup_le fun he => iSup_le fun a => ?_)
    (iSup_le fun i => ?_)
  · obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    exact le_iSup (fun i : (k : ℕ) × ↥(𝒜 (k + 1)) =>
      ProjAndSpec.specBasicOpen ((i.2 : A))) ⟨k, a⟩
  · show ProjAndSpec.specBasicOpen ((i.2 : A)) ≤
      ⨆ (e : ℕ) (_ : 0 < e) (a : 𝒜 e), ProjAndSpec.specBasicOpen ((a : A))
    exact le_iSup_of_le (i.1 + 1) (le_iSup_of_le (Nat.succ_pos i.1)
      (le_iSup (fun a : 𝒜 (i.1 + 1) => ProjAndSpec.specBasicOpen ((a : A))) i.2))

/-- **The structure morphism `L ⟶ X` is an isomorphism over `U = X ∖ V(A₊)`.** This is the
equality on the left of the diagram of [Stacks, Tag 0EKG]: being an isomorphism over an open is
local on that open, and over each standard open of a positive-degree homogeneous element the
morphism is an isomorphism. -/
@[stacks 0EKG "L → X is an isomorphism over U"]
theorem isIso_toSpecA_restrict : IsIso (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) := by
  have hle : ∀ i : (k : ℕ) × ↥(𝒜 (k + 1)),
      ProjAndSpec.specBasicOpen ((i.2 : A)) ≤ ProjAndSpec.openU 𝒜 := fun i => by
    rw [openU_eq_iSup_sigma 𝒜]
    exact le_iSup (fun j : (k : ℕ) × ↥(𝒜 (k + 1)) =>
      ProjAndSpec.specBasicOpen ((j.2 : A))) i
  have himage : ∀ i : (k : ℕ) × ↥(𝒜 (k + 1)),
      (ProjAndSpec.openU 𝒜).ι ''ᵁ
          ((ProjAndSpec.openU 𝒜).ι ⁻¹ᵁ ProjAndSpec.specBasicOpen ((i.2 : A))) =
        ProjAndSpec.specBasicOpen ((i.2 : A)) := fun i => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hle i)]
  have hsup : ⨆ i : (k : ℕ) × ↥(𝒜 (k + 1)),
      (ProjAndSpec.openU 𝒜).ι ⁻¹ᵁ ProjAndSpec.specBasicOpen ((i.2 : A)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ← openU_eq_iSup_sigma 𝒜]
    exact (ProjAndSpec.openU 𝒜).ι_preimage_self
  have hiso : MorphismProperty.isomorphisms Scheme
      (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hsup fun i => ?_
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict _ _ _)).mpr ?_
    rw [himage i]
    exact isIso_toSpecA_restrict_specBasicOpen 𝒜 (i.1 + 1) i.2.2 (Nat.succ_pos i.1)
  exact hiso

/-- **The punctured cone is the open `U`, over `X`**: the part of `L` lying over `U` maps to `X`
through the isomorphism of `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.isIso_toSpecA_restrict`
followed by the inclusion of `U`. -/
@[stacks 0EKG "the part of L over U is U, over X"]
theorem openUInL_ι_comp_toSpecA :
    (openUInL 𝒜).ι ≫ toSpecA 𝒜 =
      (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) ≫ (ProjAndSpec.openU 𝒜).ι :=
  (morphismRestrict_ι (toSpecA 𝒜) (ProjAndSpec.openU 𝒜)).symm

end IsoOverU

end Stacks.AlgebraicGeometry.ProjAndSpecTruncation

end
