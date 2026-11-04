module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.F6Rank89.RegularSurfaceWitness
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierInverseImage
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing

/-!
# The hypotheses of Tag 0BIB cannot be weakened to the literal ones

[Stacks, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB) reads: *let `X` be a regular scheme
of dimension `2` and `Z ⊂ X` a proper closed subscheme; then some sequence of blowups at closed
points turns the inverse image of `Z` into an effective Cartier divisor.* The form proved here,
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular`,
adds quasi-compactness of `X` and reads "proper" as "containing no irreducible component of
`X` of positive dimension". This file proves that both changes are forced: the statement with
either literal hypothesis in their place is false.

## Main results

* `Stacks.ResolutionOfSurfaces.not_forall_isEffectiveCartierDivisor_comap_of_isNowhereDense` —
  without quasi-compactness the statement fails, for `X` the disjoint union of countably many
  copies of `𝔸²` over `ℚ` and `Z` the union of their origins.
* `Stacks.ResolutionOfSurfaces.not_forall_isEffectiveCartierDivisor_comap_of_ne_bot` — with
  "proper" read as `Z ≠ X`, the statement fails even for Noetherian `X`, for `X = 𝔸² ⊔ 𝔸²` over
  `ℚ` and `Z` one of the two copies.

## Implementation notes

The disjoint unions are the coproducts `∐ fun _ : σ => 𝔸²` in `Scheme`, whose underlying space is
the topological disjoint union by `AlgebraicGeometry.sigmaMk`. Regularity and dimension of a
coproduct are read off from its stalks, which are those of its components because the coprojections
are open immersions. A point which is isolated in a closed set `C` has the maximal ideal as stalk
of the reduced ideal sheaf of `C`, by comparison on an affine open with the reduced closure of the
point.

## References

* [Stacks Project, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

section Coproduct

variable {σ : Type u} (f : σ → Scheme.{u})

/-- Every point of a coproduct of schemes lies in the image of one of the coprojections. -/
public theorem exists_sigmaι_eq (x : ↥(∐ f)) : ∃ (i : σ) (z : f i), Sigma.ι f i z = x := by
  obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk f).surjective x
  exact ⟨i, z, (sigmaMk_mk f i z).symm⟩

/-- A coproduct of regular schemes is regular. -/
public theorem isRegular_sigma (h : ∀ i, AlgebraicGeometry.IsRegular (f i)) :
    AlgebraicGeometry.IsRegular (∐ f) := by
  rw [isRegular_iff_regular_stalks]
  refine ⟨(isLocallyNoetherian_iff_openCover (sigmaOpenCover f)).mpr fun i =>
    ((isRegular_iff_regular_stalks (f i)).mp (h i)).1, fun x => ?_⟩
  obtain ⟨i, z, rfl⟩ := exists_sigmaι_eq f x
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (Sigma.ι f i) z).mp
    (((isRegular_iff_regular_stalks (f i)).mp (h i)).2 z)

/-- The local ring of a coproduct at a point of a component is the local ring of the component. -/
public theorem ringKrullDim_stalk_sigmaι (i : σ) (z : f i) :
    ringKrullDim ((∐ f).presheaf.stalk (Sigma.ι f i z)) = ringKrullDim ((f i).presheaf.stalk z) :=
  ringKrullDim_eq_of_ringEquiv (asIso ((Sigma.ι f i).stalkMap z)).commRingCatIsoToRingEquiv

/-- A nonempty coproduct of copies of one scheme has the dimension of that scheme. -/
public theorem topologicalKrullDim_sigma_const [Nonempty σ] (A : Scheme.{u}) :
    topologicalKrullDim ↥(∐ fun _ : σ => A) = topologicalKrullDim A := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk,
    topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun z => ?_)
  · obtain ⟨i, z, rfl⟩ := exists_sigmaι_eq (fun _ : σ => A) x
    rw [ringKrullDim_stalk_sigmaι]
    exact le_iSup (fun z : A => ringKrullDim (A.presheaf.stalk z)) z
  · obtain ⟨i⟩ := ‹Nonempty σ›
    rw [← ringKrullDim_stalk_sigmaι (fun _ : σ => A) i z]
    exact le_iSup
      (fun x : ↥(∐ fun _ : σ => A) => ringKrullDim ((∐ fun _ : σ => A).presheaf.stalk x))
      (Sigma.ι (fun _ : σ => A) i z)

/-- Points of different components, or different points of one component, are different. -/
public theorem sigmaι_eq_sigmaι_iff_const (A : Scheme.{u}) (i j : σ) (z w : A) :
    Sigma.ι (fun _ : σ => A) i z = Sigma.ι (fun _ : σ => A) j w ↔ i = j ∧ z = w := by
  rw [sigmaι_eq_iff]
  constructor
  · intro h
    obtain ⟨rfl, hzw⟩ := Sigma.mk.inj h
    exact ⟨rfl, eq_of_heq hzw⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A set of points of a coproduct of copies of `A` that meets each copy in a closed set is
closed. -/
public theorem isClosed_of_forall_isClosed_preimage_sigmaι (A : Scheme.{u})
    (C : Set ↥(∐ fun _ : σ => A))
    (hC : ∀ i, IsClosed ((Sigma.ι (fun _ : σ => A) i).base ⁻¹' C)) : IsClosed C := by
  have hC' : C = sigmaMk (fun _ : σ => A) '' (sigmaMk (fun _ : σ => A) ⁻¹' C) :=
    (Set.image_preimage_eq C (sigmaMk _).surjective).symm
  rw [hC', (sigmaMk _).isClosed_image, isClosed_sigma_iff]
  intro i
  convert hC i using 1
  ext z
  simp

/-- One point taken in each copy of `A` meets each copy in that point. -/
private theorem preimage_sigmaι_range_sigmaι_const (A : Scheme.{u}) (o : A) (n : σ) :
    (Sigma.ι (fun _ : σ => A) n).base ⁻¹' Set.range (fun m => Sigma.ι (fun _ : σ => A) m o) =
      {o} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ((sigmaι_eq_sigmaι_iff_const A m n o z).mp hm).2.symm
  · rintro rfl
    exact ⟨n, rfl⟩

/-- The image of one copy of `A` in a coproduct of copies of `A` is closed. -/
private theorem isClosed_range_sigmaι_const (A : Scheme.{u}) (i : σ) :
    IsClosed (Set.range (Sigma.ι (fun _ : σ => A) i).base) := by
  refine isClosed_of_forall_isClosed_preimage_sigmaι A _ fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [Set.preimage_range]
    exact isClosed_univ
  · convert isClosed_empty using 1
    exact Set.eq_empty_iff_forall_notMem.mpr fun z ⟨w, hw⟩ =>
      hj ((sigmaι_eq_sigmaι_iff_const A i j w z).mp hw).1.symm

end Coproduct

/-- In an irreducible scheme, a closed point whose local ring has positive dimension is not
open. -/
private theorem not_isOpen_singleton_of_ringKrullDim_stalk_ne_zero {X : Scheme.{u}}
    [IrreducibleSpace X] {o : X} (ho : IsClosed ({o} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk o) ≠ 0) : ¬ IsOpen ({o} : Set X) := by
  intro hopen
  have huniv : ({o} : Set X) = Set.univ := by
    rw [← (hopen.dense (Set.singleton_nonempty o)).closure_eq, ho.closure_eq]
  have hmax : IsMax o := fun y _ => by
    have hy : y ∈ ({o} : Set X) := huniv ▸ Set.mem_univ y
    exact (Set.mem_singleton_iff.mp hy).le
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax] at hd
  exact hd (by decide)

/-- **The reduced ideal sheaf of a closed set at an isolated point.** If a point `p` of a closed
set `C` has an open neighbourhood meeting `C` only in `p`, then the reduced closed subscheme on `C`
has the maximal ideal of `𝒪_{X,p}` as its stalk at `p`. -/
public theorem stalk_vanishingIdeal_of_inter_eq_singleton {X : Scheme.{u}} (C : Closeds X) {p : X}
    (hpC : p ∈ C) (W : X.Opens) (hpW : p ∈ W) (hW : (W : Set X) ∩ C = {p}) :
    AlgebraicGeometry.IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal C) p =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) := by
  obtain ⟨U, hU, hpU, hUW⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W) hpW
  let U' : X.affineOpens := ⟨U, hU⟩
  have hpre : ∀ T : Set X, hU.fromSpec ⁻¹' T = hU.fromSpec ⁻¹' (T ∩ (U : Set X)) := by
    intro T
    ext z
    have : hU.fromSpec z ∈ (U : Set X) := by
      rw [← hU.range_fromSpec]
      exact ⟨z, rfl⟩
    simp [this]
  have hCU : (C : Set X) ∩ U = {p} :=
    Set.Subset.antisymm (fun y hy => hW.subset ⟨hUW hy.2, hy.1⟩)
      (Set.singleton_subset_iff.mpr ⟨hpC, hpU⟩)
  have hclU : (Closeds.closure ({p} : Set X) : Set X) ∩ U = {p} :=
    Set.Subset.antisymm (fun y hy => hW.subset ⟨hUW hy.2,
      closure_minimal (Set.singleton_subset_iff.mpr hpC) C.isClosed hy.1⟩)
      (Set.singleton_subset_iff.mpr ⟨subset_closure rfl, hpU⟩)
  have hideal : (Scheme.IdealSheafData.vanishingIdeal C).ideal U' =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({p} : Set X))).ideal U' := by
    change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (C : Set X)) =
      PrimeSpectrum.vanishingIdeal
        (hU.fromSpec ⁻¹' (Closeds.closure ({p} : Set X) : Set X))
    have e1 : hU.fromSpec ⁻¹' (C : Set X) =
        hU.fromSpec ⁻¹' (Closeds.closure ({p} : Set X) : Set X) := by
      rw [hpre (C : Set X), hpre (Closeds.closure ({p} : Set X) : Set X), hCU, hclU]
    exact congrArg _ e1
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ p U' hpU, hideal,
    ← AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ p U' hpU]
  exact Stacks.Divisors.stalk_vanishingIdeal_closure_singleton p

section AffinePlane

variable (k : Type u) [Field k]

/-- The affine plane `𝔸²_k` is regular. -/
public theorem isRegular_affinePlane :
    AlgebraicGeometry.IsRegular (Spec (.of (MvPolynomial (Fin 2) k))) :=
  isRegular_Spec_mvPolynomial k 2

/-- The affine plane `𝔸²_k` has dimension two. -/
public theorem topologicalKrullDim_affinePlane :
    topologicalKrullDim ↥(Spec (.of (MvPolynomial (Fin 2) k))) = 2 := by
  rw [topologicalKrullDim_Spec_mvPolynomial]
  rfl

/-- The affine plane `𝔸²_k` has a closed point with a two-dimensional local ring. -/
public theorem exists_isClosed_ringKrullDim_stalk_affinePlane :
    ∃ o : Spec (.of (MvPolynomial (Fin 2) k)),
      IsClosed ({o} : Set (Spec (.of (MvPolynomial (Fin 2) k)))) ∧
        ringKrullDim ((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk o) = 2 := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (MvPolynomial (Fin 2) k)
  let o : Spec (.of (MvPolynomial (Fin 2) k)) := (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum _)
  refine ⟨o, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr h𝔪, ?_⟩
  let : Algebra (MvPolynomial (Fin 2) k) ((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk o) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of (MvPolynomial (Fin 2) k)) o
  have : IsLocalization.AtPrime ((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk o) 𝔪 :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (MvPolynomial (Fin 2) k)) o
  have h :=
    ((MvPolynomial.isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization
      k (Fin 2)).2.2 𝔪 ((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk o)).2
  rw [h]
  simp

/-- Over an infinite field the affine plane `𝔸²_k` has infinitely many points. -/
public theorem infinite_affinePlane [Infinite k] :
    Infinite (Spec (.of (MvPolynomial (Fin 2) k))) := by
  let ev : k → MvPolynomial (Fin 2) k →+* k := fun a => MvPolynomial.eval ![a, 0]
  let e : k → Spec (.of (MvPolynomial (Fin 2) k)) := fun a =>
    (⟨RingHom.ker (ev a), RingHom.ker_isPrime _⟩ : PrimeSpectrum _)
  refine Infinite.of_injective e fun a b hab => ?_
  have hmem : (MvPolynomial.X 0 - MvPolynomial.C a) ∈ RingHom.ker (ev a) := by
    simp [ev, RingHom.mem_ker]
  have h' : RingHom.ker (ev a) = RingHom.ker (ev b) := congrArg PrimeSpectrum.asIdeal hab
  have hb := h' ▸ hmem
  rw [RingHom.mem_ker] at hb
  simp only [ev, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero,
    sub_eq_zero] at hb
  exact hb.symm

end AffinePlane

/-- A nonempty coproduct of copies of `𝔸²_k` is regular of dimension two. -/
private theorem isRegular_and_topologicalKrullDim_sigma_affinePlane (σ : Type u) [Nonempty σ]
    (k : Type u) [Field k] :
    AlgebraicGeometry.IsRegular (∐ fun _ : σ => Spec (.of (MvPolynomial (Fin 2) k))) ∧
      topologicalKrullDim ↥(∐ fun _ : σ => Spec (.of (MvPolynomial (Fin 2) k))) = 2 :=
  ⟨isRegular_sigma _ fun _ => isRegular_affinePlane k,
    (topologicalKrullDim_sigma_const _).trans (topologicalKrullDim_affinePlane k)⟩

/-- **Quasi-compactness cannot be dropped from Tag 0BIB.** The statement of
[Stacks, Tag 0BIB] for a regular scheme of dimension `2` which is not assumed quasi-compact — with
"proper closed subscheme" in its strongest reading, containing no irreducible component — is
false. For `X` the disjoint union of countably many copies of `𝔸²` over `ℚ` and `Z` the reduced
union of one closed point in each copy, `Z` is nowhere dense, but a finite sequence of blowups at
closed points leaves some copy untouched, where the ideal of the inverse image of `Z` is the
maximal ideal of a two-dimensional regular local ring
(`not_isEffectiveCartierDivisor_comap_of_infinite`).
The corrected statement is
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular`.
-/
public theorem not_forall_isEffectiveCartierDivisor_comap_of_isNowhereDense :
    ¬ ∀ (X : Scheme.{u}), AlgebraicGeometry.IsRegular X → topologicalKrullDim X = 2 →
      ∀ Z : X.IdealSheafData, IsNowhereDense (Z.support : Set X) →
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X Set.univ Y f ∧
          Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  intro H
  let A : Scheme.{u} := Spec (.of (MvPolynomial (Fin 2) (ULift.{u} ℚ)))
  let F : ULift.{u} ℕ → Scheme.{u} := fun _ => A
  let X : Scheme.{u} := ∐ F
  obtain ⟨o, ho, hodim⟩ := exists_isClosed_ringKrullDim_stalk_affinePlane (ULift.{u} ℚ)
  let p : ULift.{u} ℕ → X := fun n => Sigma.ι F n o
  have hpinj : Function.Injective p := fun m n h =>
    ((sigmaι_eq_sigmaι_iff_const A m n o o).mp h).1
  have hpre : ∀ n, (Sigma.ι F n).base ⁻¹' Set.range p = {o} :=
    preimage_sigmaι_range_sigmaι_const A o
  have hPclosed : IsClosed (Set.range p) :=
    isClosed_of_forall_isClosed_preimage_sigmaι A _ fun n => by rwa [hpre n]
  let P : Closeds X := ⟨Set.range p, hPclosed⟩
  let Z : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal P
  have hsupp : (Z.support : Set X) = Set.range p := by
    simp [Z, Scheme.IdealSheafData.coe_support_vanishingIdeal, P]
  obtain ⟨hreg, hdim⟩ := isRegular_and_topologicalKrullDim_sigma_affinePlane (ULift.{u} ℕ)
    (ULift.{u} ℚ)
  have hnd : IsNowhereDense (Z.support : Set X) := by
    rw [hsupp, hPclosed.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨n, rfl⟩ := interior_subset hx
    refine not_isOpen_singleton_of_ringKrullDim_stalk_ne_zero (X := A) ho
      (by rw [hodim]; decide) ?_
    convert isOpen_interior.preimage (Sigma.ι F n).continuous using 1
    exact Set.Subset.antisymm (Set.singleton_subset_iff.mpr hx)
      ((Set.preimage_mono interior_subset).trans (hpre n).subset)
  obtain ⟨Y, f, hf, hcart⟩ := H X hreg hdim Z hnd
  refine not_isEffectiveCartierDivisor_comap_of_infinite hf Z (Set.range p)
    (Set.infinite_range_of_injective hpinj) ?_ ?_ ?_ hcart
  · rintro _ ⟨n, rfl⟩
    exact ((isRegular_iff_regular_stalks X).mp hreg).2 _
  · rintro _ ⟨n, rfl⟩
    rw [ringKrullDim_stalk_sigmaι]
    exact hodim
  · rintro _ ⟨n, rfl⟩
    refine stalk_vanishingIdeal_of_inter_eq_singleton P ⟨n, rfl⟩ (Sigma.ι F n).opensRange
      ⟨o, rfl⟩ ?_
    refine Set.Subset.antisymm (fun y hy => ?_) ?_
    · obtain ⟨⟨z, rfl⟩, hzP⟩ := hy
      exact congrArg (Sigma.ι F n).base (Set.mem_singleton_iff.mp ((hpre n).subset hzP))
    · rintro y rfl
      exact ⟨⟨o, rfl⟩, ⟨n, rfl⟩⟩

/-- **"Proper closed subscheme" cannot be read as `Z ≠ X` in Tag 0BIB.** The statement of
[Stacks, Tag 0BIB] for a Noetherian regular scheme of dimension `2` and a closed subscheme
`Z ≠ X` — even one whose support is not all of `X` — is false. For `X = 𝔸² ⊔ 𝔸²` over `ℚ` and `Z`
the first copy, the first copy is an infinite open subset of `X` inside `Z`, and no sequence of
blowups at closed points turns such a `Z` into an effective Cartier divisor
(`finite_of_isOpen_subset_support_of_pointBlowupChain`); the first copy is an irreducible
component of dimension two. The corrected statement, with `Z` containing no irreducible
component of `X` of positive dimension, is
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular`.
-/
public theorem not_forall_isEffectiveCartierDivisor_comap_of_ne_bot :
    ¬ ∀ (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X], AlgebraicGeometry.IsRegular X →
      topologicalKrullDim X = 2 → ∀ Z : X.IdealSheafData, Z ≠ ⊥ →
        (Z.support : Set X) ≠ Set.univ →
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X Set.univ Y f ∧
          Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  intro H
  let A : Scheme.{u} := Spec (.of (MvPolynomial (Fin 2) (ULift.{u} ℚ)))
  let F : ULift.{u} (Fin 2) → Scheme.{u} := fun _ => A
  let X : Scheme.{u} := ∐ F
  obtain ⟨o, -, -⟩ := exists_isClosed_ringKrullDim_stalk_affinePlane (ULift.{u} ℚ)
  let C : Set X := Set.range (Sigma.ι F ⟨0⟩).base
  have hCclosed : IsClosed C := isClosed_range_sigmaι_const A (⟨0⟩ : ULift.{u} (Fin 2))
  let Z : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, hCclosed⟩
  have hsupp : (Z.support : Set X) = C := by
    simp [Z, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hne : (Z.support : Set X) ≠ Set.univ := by
    rw [hsupp]
    intro h
    obtain ⟨w, hw⟩ : Sigma.ι F (⟨1⟩ : ULift.{u} (Fin 2)) o ∈ C := h ▸ Set.mem_univ _
    exact absurd ((sigmaι_eq_sigmaι_iff_const A (⟨0⟩ : ULift.{u} (Fin 2)) ⟨1⟩ w o).mp hw).1
      (by simp)
  have hbot : Z ≠ ⊥ := by
    intro h
    apply hne
    rw [h, Scheme.IdealSheafData.support_bot]
    rfl
  obtain ⟨hreg, hdim⟩ :=
    isRegular_and_topologicalKrullDim_sigma_affinePlane (ULift.{u} (Fin 2)) (ULift.{u} ℚ)
  have : IsLocallyNoetherian X := ((isRegular_iff_regular_stalks X).mp hreg).1
  have : CompactSpace X := (sigmaMk F).compactSpace
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨Y, f, hf, hcart⟩ := H X hreg hdim Z hbot hne
  have hfin : C.Finite :=
    finite_of_isOpen_subset_support_of_pointBlowupChain hf Z hcart
      (Sigma.ι F ⟨0⟩).isOpenEmbedding.isOpen_range hsupp.symm.subset
  have := infinite_affinePlane (ULift.{u} ℚ)
  exact Set.infinite_range_of_injective (Sigma.ι F ⟨0⟩).isOpenEmbedding.injective hfin

end Stacks.ResolutionOfSurfaces

end
