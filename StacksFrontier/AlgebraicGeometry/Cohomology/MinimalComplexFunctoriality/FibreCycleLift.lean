module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Homology.DerivedCategory.KProjectiveHomotopyEquiv
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHomRestrictKFlat
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution

/-!
# Lifting a degree-zero class of the derived fibre: the matrix argument of Tag 0BF2

Let `χ : R ⟶ K` be a homomorphism from a commutative ring to a field and let `M`, `N k` (`k` in a
finite type) be perfect objects of `D(R)` with maps `ψ k : M ⟶ N k`. The proofs of
[Stacks, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1) and
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2) show, by representing `M`, the
`N k` and the `ψ k` by maps of minimal complexes of finite free modules near the prime
`ker χ` ([Stacks, Tag 0BCD]), that a degree-zero class of the fibre `M ⊗ᴸ_R K` lifts to `M` as
soon as the maps `H¹(ψ k ⊗ᴸ K)` are jointly injective and each `N k` has a one-dimensional
`H⁰` of its fibre reached from `R`: in the source, `d_k = 0` because `L_k` is trivial, the
injectivity makes the matrix `(b_k)` injective near the prime, and so `d = 0`.

This file proves that argument in the derived category of `R`-modules.

## Main results

* `StacksDraft.Perfect.FibreCycleLift.d_zero_one_eq_zero`: the core, over a local ring, for
  complexes of finite free modules with minimal fibres.
* `StacksDraft.Perfect.FibreCycleLift.exists_minimal_model`: a minimal model of a bounded complex
  of finite projective modules over a local ring, from [Stacks, Tag 0BCC].
* `StacksDraft.Perfect.FibreCycleLift.exists_unit_map_homologyMap_ne_zero`: the argument for
  bounded complexes of finite projective `R`-modules.
* `StacksDraft.Perfect.FibreCycleLift.exists_unit_map_derived_ne_zero`: the argument for perfect
  objects of `D(R)`, with an arbitrary total derived extension of scalars along `χ`.

## Implementation notes

The prime is `ker χ` and the argument runs over the localization `R_p` (`Loc χ`), where minimal
models exist; a cycle of the minimal model is carried back to `R` by clearing denominators. The
field `K` need not be the residue field of `p`: minimality is detected over the residue field of
`R_p`, where Tag 0BCC computes the ranks, and the rest of the argument runs over `K`.

## References

* [Stacks Project, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1)
* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace StacksDraft.Perfect.FibreCycleLift

section Basic

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] (χ : A →+* S)

/-- `S` regarded as an `A`-module along `χ`, the left factor of `S ⊗_A M`. -/
abbrev fibreScalars : ModuleCat.{u} A := (ModuleCat.restrictScalars χ).obj (ModuleCat.of S S)

/-- The image `1 ⊗ x` of `x : M` in the base change `S ⊗_A M`. -/
def fibreElt (M : ModuleCat.{u} A) (x : M) : (ModuleCat.extendScalars χ).obj M :=
  TensorProduct.tmul A (show fibreScalars χ from (1 : S)) x

/-- The map `x ↦ 1 ⊗ x` is additive. -/
theorem fibreElt_add (M : ModuleCat.{u} A) (x y : M) :
    fibreElt χ M (x + y) = fibreElt χ M x + fibreElt χ M y :=
  TensorProduct.tmul_add _ _ _

/-- The map `x ↦ 1 ⊗ x` sends `a • x` to `χ a • (1 ⊗ x)`. -/
theorem fibreElt_smul (M : ModuleCat.{u} A) (a : A) (x : M) :
    fibreElt χ M (a • x) = χ a • fibreElt χ M x := by
  change TensorProduct.tmul A _ (a • x) =
    TensorProduct.tmul A (χ a • (show fibreScalars χ from (1 : S))) x
  rw [← TensorProduct.smul_tmul]
  rfl

/-- The base change of `g : M ⟶ N` sends `1 ⊗ x` to `1 ⊗ g x`. -/
theorem map_fibreElt {M N : ModuleCat.{u} A} (g : M ⟶ N) (x : M) :
    (ModuleCat.extendScalars χ).map g (fibreElt χ M x) = fibreElt χ N (g x) := rfl

/-- The elements `1 ⊗ x` span the base change `S ⊗_A M`. -/
theorem fibreElt_span (M : ModuleCat.{u} A) :
    (Submodule.span S (Set.range (fibreElt χ M)) : Submodule S ((ModuleCat.extendScalars χ).obj M))
      = ⊤ := by
  let N : Submodule S ((ModuleCat.extendScalars χ).obj M) :=
    Submodule.span S (Set.range (fibreElt χ M))
  have hq : (ModuleCat.ofHom (X := ((ModuleCat.extendScalars χ).obj M : Type u)) N.mkQ :
      (ModuleCat.extendScalars χ).obj M ⟶ ModuleCat.of S (↑((ModuleCat.extendScalars χ).obj M) ⧸ N))
      = 0 := by
    refine ModuleCat.ExtendScalars.hom_ext fun x => ?_
    change N.mkQ (fibreElt χ M x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, rfl⟩
  rw [eq_top_iff]
  intro c _
  have h0 : N.mkQ c = 0 := congrArg (fun φ => φ.hom c) hq
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0

/-- Every element of the base change `S ⊗_A M` lies in the span of the elements `1 ⊗ x`. -/
private theorem mem_span_range_fibreElt (M : ModuleCat.{u} A)
    (c : (ModuleCat.extendScalars χ).obj M) :
    c ∈ Submodule.span S (Set.range (fibreElt χ M)) := by
  rw [fibreElt_span]
  exact Submodule.mem_top

/-- A nontrivial base change `S ⊗_A M` contains an element `1 ⊗ x` which is nonzero. -/
private theorem exists_fibreElt_ne_zero (M : ModuleCat.{u} A)
    [Nontrivial ((ModuleCat.extendScalars χ).obj M)] : ∃ x : M, fibreElt χ M x ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨v, hv⟩ := exists_ne (0 : (ModuleCat.extendScalars χ).obj M)
  apply hv
  have hle : (Submodule.span S (Set.range (fibreElt χ M)) :
      Submodule S ((ModuleCat.extendScalars χ).obj M)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hall m
  rw [fibreElt_span] at hle
  exact (Submodule.eq_bot_iff _).1 (le_bot_iff.1 hle) v Submodule.mem_top

/-- An isomorphism of modules sends only `0` to `0`. -/
private theorem eq_zero_of_iso_hom_apply_eq_zero {M N : ModuleCat.{u} A} (e : M ≅ N) {x : M}
    (hx : e.hom x = 0) : x = 0 := by
  have := congrArg e.inv hx
  rwa [← ModuleCat.comp_apply, e.hom_inv_id, map_zero] at this

/-- Joint injectivity of a family of maps of modules transfers along isomorphisms of their
sources and targets. -/
private theorem eq_zero_of_forall_map_eq_zero_of_iso {ι : Type*} {M M' : ModuleCat.{u} A}
    {N N' : ι → ModuleCat.{u} A} (eM : M ≅ M') (eN : ∀ k, N k ≅ N' k) (f : ∀ k, M ⟶ N k)
    (f' : ∀ k, M' ⟶ N' k) (hf : ∀ k, eM.hom ≫ f' k = f k ≫ (eN k).hom)
    (h : ∀ c, (∀ k, f k c = 0) → c = 0) (c : M') (hc : ∀ k, f' k c = 0) : c = 0 := by
  have hc' : eM.inv c = 0 := by
    refine h _ fun k => ?_
    have := congrArg (fun φ => φ.hom (eM.inv c)) (hf k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [← ModuleCat.comp_apply eM.inv eM.hom, Iso.inv_hom_id, ModuleCat.id_apply, hc k] at this
    exact eq_zero_of_iso_hom_apply_eq_zero (eN k) this.symm
  exact eq_zero_of_iso_hom_apply_eq_zero eM.symm hc'

/-- The base change `S ⊗_A F` of a cochain complex of `A`-modules. -/
abbrev fibreComplex (F : CochainComplex (ModuleCat.{u} A) ℤ) : CochainComplex (ModuleCat.{u} S) ℤ :=
  ((ModuleCat.extendScalars χ).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- The base change `S ⊗_A φ` of a map of cochain complexes of `A`-modules. -/
abbrev fibreMap {F G : CochainComplex (ModuleCat.{u} A) ℤ} (φ : F ⟶ G) :
    fibreComplex χ F ⟶ fibreComplex χ G :=
  ((ModuleCat.extendScalars χ).mapHomologicalComplex (ComplexShape.up ℤ)).map φ

end Basic

section LinearAlgebra

variable {A : Type u} [CommRing A] {K : Type u} [Field K] (χ : A →+* K)

/-- An element of the maximal-ideal multiple vanishes in every fibre. -/
theorem fibreElt_eq_zero_of_mem [IsLocalRing A] [IsLocalHom χ] (M : ModuleCat.{u} A) (x : M)
    (hx : x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
    fibreElt χ M x = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha m _
    have h0 : χ a = 0 := by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).1 ha ((isUnit_map_iff χ a).1 (IsUnit.mk0 _ h))
    rw [fibreElt_smul, h0, zero_smul]
  · intro x y hx hy
    rw [fibreElt_add, hx, hy, add_zero]

/-- **For a free module the fibre detects the maximal-ideal multiple.** -/
theorem mem_of_fibreElt_eq_zero [IsLocalRing A] [IsLocalHom χ] (M : ModuleCat.{u} A)
    [Module.Free A M] (x : M) (hx : fibreElt χ M x = 0) :
    x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
  classical
  let b := Module.Free.chooseBasis A M
  let e : fibreScalars χ ⊗[A] M ≃ₗ[A] (Module.Free.ChooseBasisIndex A M →₀ fibreScalars χ) :=
    (b.repr.lTensor (fibreScalars χ)).trans (TensorProduct.finsuppScalarRight A A _ _)
  have hcoord : ∀ i, χ (b.repr x i) = 0 := by
    intro i
    have h1 : e (TensorProduct.tmul A (show fibreScalars χ from (1 : K)) x) i = 0 := by
      have : TensorProduct.tmul A (show fibreScalars χ from (1 : K)) x = 0 := hx
      rw [this, map_zero]
      rfl
    have h2 : e (TensorProduct.tmul A (show fibreScalars χ from (1 : K)) x) i =
        (b.repr x i) • (show fibreScalars χ from (1 : K)) := by
      simp only [e, LinearEquiv.trans_apply]
      exact TensorProduct.finsuppScalarRight_apply_tmul_apply _ _ _
    rw [h2] at h1
    have h3 : ((b.repr x i) • (show fibreScalars χ from (1 : K)) : K) = χ (b.repr x i) * 1 := rfl
    rw [h3] at h1
    have h4 : (χ (b.repr x i) * 1 : K) = 0 := h1
    simpa using h4
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact ((isUnit_map_iff χ _).2 hu).ne_zero (hcoord i)

/-- **A rank-one free module is generated by any element with nonzero fibre**, so a linear map
killing such an element is zero. -/
theorem eq_zero_of_apply_eq_zero_of_finrank_le_one [IsLocalRing A] [IsLocalHom χ]
    (M : ModuleCat.{u} A) [Module.Free A M] [Module.Finite A M]
    (hM : Module.finrank A M ≤ 1) (z : M) (hz : fibreElt χ M z ≠ 0)
    {N : Type u} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (hf : f z = 0) : f = 0 := by
  have hzm : z ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) :=
    fun h => hz (fibreElt_eq_zero_of_mem χ M z h)
  have hpos : Module.finrank A M ≠ 0 := by
    intro h0
    obtain rfl : z = 0 := (Module.finBasisOfFinrankEq A M h0).ext_elem fun i => i.elim0
    exact hzm (Submodule.zero_mem _)
  have h1 : Module.finrank A M = 1 := by omega
  let b := Module.finBasisOfFinrankEq A M h1
  have hz' : z = b.repr z 0 • b 0 := by
    conv_lhs => rw [← b.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have hu : IsUnit (b.repr z 0) := by
    by_contra h
    apply hzm
    rw [hz']
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).2 h) Submodule.mem_top
  refine b.ext fun i => ?_
  obtain rfl : i = 0 := Subsingleton.elim i 0
  have : f (b.repr z 0 • b 0) = 0 := by rwa [← hz']
  rw [map_smul] at this
  rw [LinearMap.zero_apply]
  exact (hu.smul_left_cancel).1 (this.trans (smul_zero _).symm)

/-- **Injectivity in the fibre gives injectivity.** For a linear map of finite free modules over
a local ring, injectivity after extension of scalars along a local homomorphism to a field
implies injectivity: it gives injectivity modulo the maximal ideal, and then
`IsLocalRing.split_injective_iff_lTensor_residueField_injective` applies. -/
theorem injective_of_injective_extendScalars_map [IsLocalRing A] [IsLocalHom χ]
    {M N : ModuleCat.{u} A} [Module.Free A M] [Module.Finite A M] [Module.Free A N]
    [Module.Finite A N] (g : M ⟶ N)
    (hg : Function.Injective ((ModuleCat.extendScalars χ).map g)) : Function.Injective g := by
  have hmod : ∀ x : M, g x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) →
      x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
    intro x hx
    refine mem_of_fibreElt_eq_zero χ M x (hg ?_)
    rw [map_fibreElt, map_zero]
    exact fibreElt_eq_zero_of_mem χ N _ hx
  let m := IsLocalRing.maximalIdeal A
  have hk : Function.Injective (g.hom.lTensor (A ⧸ m)) := by
    intro y y' hyy'
    rw [← sub_eq_zero, ← map_sub] at hyy'
    rw [← sub_eq_zero]
    obtain ⟨x, hx⟩ : ∃ x : M, (TensorProduct.quotTensorEquivQuotSMul M m).symm
        (Submodule.Quotient.mk x) = y - y' :=
      ⟨_, (Submodule.Quotient.mk_surjective _ ((TensorProduct.quotTensorEquivQuotSMul M m)
        (y - y'))).choose_spec ▸ (LinearEquiv.symm_apply_apply _ _)⟩
    rw [← hx] at hyy' ⊢
    rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk] at hyy' ⊢
    have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul N m) hyy'
    rw [LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
      map_zero, Submodule.Quotient.mk_eq_zero] at h2
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, map_eq_zero_iff _
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.injective,
      Submodule.Quotient.mk_eq_zero]
    exact hmod x h2
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective g.hom).2 hk
  exact Function.HasLeftInverse.injective ⟨l', fun x => LinearMap.congr_fun hl' x⟩

end LinearAlgebra

section ZeroDifferentials

variable {C : Type*} [Category C] [Abelian C]

/-- In a cochain complex whose differentials all vanish, each term is its own cohomology. -/
def zeroDiffHomologyIso (V : CochainComplex C ℤ) (hV : ∀ i j, V.d i j = 0) (i : ℤ) :
    V.X i ≅ V.homology i :=
  (V.iCyclesIso i (i + 1) (by simp) (hV _ _)).symm ≪≫
    V.isoHomologyπ (i - 1) i (by simp) (hV _ _)

/-- The identification `zeroDiffHomologyIso` is natural. -/
theorem zeroDiffHomologyIso_hom_naturality {V W : CochainComplex C ℤ} (hV : ∀ i j, V.d i j = 0)
    (hW : ∀ i j, W.d i j = 0) (φ : V ⟶ W) (i : ℤ) :
    (zeroDiffHomologyIso V hV i).hom ≫ HomologicalComplex.homologyMap φ i =
      φ.f i ≫ (zeroDiffHomologyIso W hW i).hom := by
  have h1 : (V.iCyclesIso i (i + 1) (by simp) (hV _ _)).inv ≫
      HomologicalComplex.cyclesMap φ i =
      φ.f i ≫ (W.iCyclesIso i (i + 1) (by simp) (hW _ _)).inv := by
    rw [← cancel_mono (W.iCycles i)]
    simp
  simp only [zeroDiffHomologyIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.homologyπ_naturality]
  rw [reassoc_of% h1]

/-- Two maps between complexes with zero differentials which agree on cohomology in some degree
agree in that degree. -/
private theorem f_eq_of_homologyMap_eq {V W : CochainComplex C ℤ} (hV : ∀ i j, V.d i j = 0)
    (hW : ∀ i j, W.d i j = 0) {φ ψ : V ⟶ W} {i : ℤ}
    (h : HomologicalComplex.homologyMap φ i = HomologicalComplex.homologyMap ψ i) :
    φ.f i = ψ.f i := by
  rw [← cancel_mono (zeroDiffHomologyIso W hW i).hom]
  have hn := zeroDiffHomologyIso_hom_naturality hV hW φ i
  rw [h, zeroDiffHomologyIso_hom_naturality hV hW ψ i] at hn
  exact hn.symm

/-- A map between complexes with zero differentials which is nonzero in some degree is nonzero
on cohomology in that degree. -/
private theorem homologyMap_ne_zero_of_f_ne_zero {V W : CochainComplex C ℤ}
    (hV : ∀ i j, V.d i j = 0) (hW : ∀ i j, W.d i j = 0) (φ : V ⟶ W) (i : ℤ) (h : φ.f i ≠ 0) :
    HomologicalComplex.homologyMap φ i ≠ 0 := fun h0 =>
  h (f_eq_of_homologyMap_eq hV hW (ψ := 0) (by rw [h0, HomologicalComplex.homologyMap_zero]))

end ZeroDifferentials

section HomotopyEquiv

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] (χ : A →+* S)

/-- If the fibre of `F` has zero differentials, then the fibre of `h.hom ≫ h.inv` is the identity
in each degree, for any homotopy equivalence `h` out of `F`. -/
private theorem fibreMap_homotopyEquiv_hom_inv_f {F P : CochainComplex (ModuleCat.{u} A) ℤ}
    (h : HomotopyEquiv F P) (hF : ∀ i j, (fibreComplex χ F).d i j = 0) (i : ℤ) :
    (fibreMap χ (h.hom ≫ h.inv)).f i = 𝟙 _ := by
  let e := (ModuleCat.extendScalars χ).mapHomotopyEquiv h (c := ComplexShape.up ℤ)
  have : fibreMap χ (h.hom ≫ h.inv) = e.hom ≫ e.inv := Functor.map_comp _ _ _
  exact f_eq_of_homologyMap_eq hF hF (ψ := 𝟙 _)
    (by rw [this, e.homotopyHomInvId.homologyMap_eq, HomologicalComplex.homologyMap_id])

end HomotopyEquiv

section Core

variable {A : Type u} [CommRing A] [IsLocalRing A] {K : Type u} [Field K] (χ : A →+* K)
  [IsLocalHom χ]

/-- **The core of the matrix argument of Tag 0BF2, over a local ring.** Let `F` and `G k`
(`k` in a finite type) be complexes of finite free modules over the local ring `A` whose fibres
along the local homomorphism `χ : A ⟶ K` to a field have zero differentials, and let
`θ k : F ⟶ G k` be maps of complexes. If the fibres of the `θ k` in degree `1` are jointly
injective, and each `G k` has a degree-`0` cycle of nonzero fibre in a term of rank at most one,
then the differential `F⁰ ⟶ F¹` vanishes. -/
theorem d_zero_one_eq_zero (F : CochainComplex (ModuleCat.{u} A) ℤ)
    [∀ i, Module.Free A (F.X i)] [∀ i, Module.Finite A (F.X i)]
    {ι : Type u} [Finite ι] (G : ι → CochainComplex (ModuleCat.{u} A) ℤ)
    [∀ k i, Module.Free A ((G k).X i)] [∀ k i, Module.Finite A ((G k).X i)]
    (θ : ∀ k, F ⟶ G k)
    (h1 : ∀ x : (fibreComplex χ F).X 1,
      (∀ k, (ModuleCat.extendScalars χ).map ((θ k).f 1) x = 0) → x = 0)
    (hdim : ∀ k, Module.finrank A ((G k).X 0) ≤ 1)
    (hz : ∀ k, ∃ z : (G k).X 0, (G k).d 0 1 z = 0 ∧ fibreElt χ _ z ≠ 0) :
    F.d 0 1 = 0 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hG : ∀ k, (G k).d 0 1 = 0 := by
    intro k
    obtain ⟨z, hz0, hzf⟩ := hz k
    exact ModuleCat.hom_ext (eq_zero_of_apply_eq_zero_of_finrank_le_one χ _ (hdim k) z hzf
      ((G k).d 0 1).hom hz0)
  let P : ModuleCat.{u} A := ModuleCat.of A (∀ k, (G k).X 1)
  let b : F.X 1 ⟶ P := ModuleCat.ofHom (LinearMap.pi fun k => ((θ k).f 1).hom)
  have hb : Function.Injective b := by
    refine injective_of_injective_extendScalars_map χ b ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine h1 x fun k => ?_
    have hk : (θ k).f 1 = b ≫ ModuleCat.ofHom (LinearMap.proj k) := by
      ext y
      rfl
    rw [hk, Functor.map_comp, ModuleCat.comp_apply]
    change (ModuleCat.extendScalars χ).map _ (((ModuleCat.extendScalars χ).map b).hom x) = 0
    rw [hx, map_zero]
  have hcomp : ∀ k, F.d 0 1 ≫ (θ k).f 1 = 0 := by
    intro k
    rw [← (θ k).comm, hG k, comp_zero]
  ext x
  apply hb
  change b (F.d 0 1 x) = b 0
  rw [map_zero]
  funext k
  exact congrArg (fun φ => φ.hom x) (hcomp k)

omit [IsLocalRing A] [IsLocalHom χ] in
/-- The fibre of a finite free standard module has the expected dimension. -/
theorem finrank_fibre_ulift {L : Type u} [Field L] (ρ : A →+* L) (n : ℕ)
    (M : ModuleCat.{u} A) (e : M ≅ ModuleCat.of A (ULift.{u} (Fin n → A))) :
    Module.finrank L ((ModuleCat.extendScalars ρ).obj M) = n ∧
      FiniteDimensional L ((ModuleCat.extendScalars ρ).obj M) := by
  obtain ⟨e'⟩ := StacksDraft.Perfect.extendScalars_standard_free_iso.{u, u} ρ n
  let E := ((ModuleCat.extendScalars ρ).mapIso e ≪≫ e').toLinearEquiv
  refine ⟨?_, ?_⟩
  · rw [E.finrank_eq, ULift.moduleEquiv.finrank_eq, Module.finrank_fin_fun]
  · exact LinearEquiv.finiteDimensional E.symm

/-- **A complex of finite free modules over a local ring whose terms have the ranks of the
cohomology of its residual fibre is minimal**: the differentials of each of its fibres vanish. -/
theorem fibreComplex_d_eq_zero (F : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℤ → ℕ)
    (hF : ∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A))))
    (hH : ∀ i, Module.finrank (IsLocalRing.ResidueField A)
      ((fibreComplex (IsLocalRing.residue A) F).homology i) = r i) :
    ∀ i j, (fibreComplex χ F).d i j = 0 := by
  let ρ := IsLocalRing.residue A
  let V := fibreComplex ρ F
  have hfree : ∀ i, Module.Free A (F.X i) := fun i =>
    Module.Free.of_equiv ((hF i).some.toLinearEquiv.symm)
  have hV : ∀ i, V.d i (i + 1) = 0 := by
    intro i
    obtain ⟨hrk, hfd⟩ := finrank_fibre_ulift ρ (r i) (F.X i) (hF i).some
    let S := V.sc i
    have : FiniteDimensional (IsLocalRing.ResidueField A) S.X₂ := hfd
    have hH' : Module.finrank (IsLocalRing.ResidueField A)
        (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = r i := by
      rw [← hH i]
      exact (S.moduleCatHomologyIso.toLinearEquiv.finrank_eq).symm
    have hle1 := Submodule.finrank_quotient_le (LinearMap.range S.moduleCatToCycles)
    have hle2 := Submodule.finrank_le (LinearMap.ker S.g.hom)
    have hrk' : Module.finrank (IsLocalRing.ResidueField A) S.X₂ = r i := hrk
    have heq : Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker S.g.hom) =
        Module.finrank (IsLocalRing.ResidueField A) S.X₂ := by
      omega
    have htop := Submodule.eq_top_of_finrank_eq heq
    have key : S.g = 0 := by
      ext x
      have hx : x ∈ LinearMap.ker S.g.hom := htop ▸ Submodule.mem_top
      exact hx
    have key' : V.d i ((ComplexShape.up ℤ).next i) = 0 := key
    rwa [CochainComplex.next] at key'
  intro i j
  by_cases hij : j = i + 1
  · subst hij
    refine ModuleCat.ExtendScalars.hom_ext fun x => ?_
    change (ModuleCat.extendScalars χ).map (F.d i (i + 1)) (fibreElt χ _ x) = 0
    rw [map_fibreElt]
    have : Module.Free A (F.X (i + 1)) := hfree _
    refine fibreElt_eq_zero_of_mem χ _ _ (mem_of_fibreElt_eq_zero ρ _ _ ?_)
    exact congrArg (fun φ => φ.hom (fibreElt ρ _ x)) (hV i)
  · exact (fibreComplex χ F).shape _ _ (by simp [ComplexShape.up_Rel]; omega)

end Core

section MinimalModel

attribute [local instance 10000] HasDerivedCategory.standard

open CochainComplex.DerivedExtensionScalars

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **A minimal model over a local ring** ([Stacks, Tag 0BCC]). A bounded complex `P` of finite
free modules over a local ring is homotopy equivalent to a complex `F` whose term in degree `i`
is free of rank `r i`, where `r i` is the dimension of the degree-`i` cohomology of the residual
fibre of `F`. -/
theorem exists_minimal_model (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite A (P.X i)) (hproj : ∀ i, Module.Projective A (P.X i)) :
    ∃ (F : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℤ → ℕ),
      (∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A)))) ∧
      (∀ i, Module.finrank (IsLocalRing.ResidueField A)
        ((fibreComplex (IsLocalRing.residue A) F).homology i) = r i) ∧
      Nonempty (HomotopyEquiv F P) := by
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj P) :=
    ⟨P, a, b, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩
  obtain ⟨-, c, -, F, hFc, ⟨hX, ⟨eF⟩⟩, -⟩ :=
    StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing.{u, u}
      (DerivedCategory.Q.obj P)
      (StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _ hperf)
  let D := totalDerivedExtensionScalars.{u, u, u} (IsLocalRing.residue A)
  have hFproj : ∀ i, Projective (F.X i) := fun i =>
    Projective.of_iso (hX i).some.symm (ModuleCat.projective_of_free
      ((Pi.basisFun A _).map ULift.moduleEquiv.symm))
  have hPproj : ∀ i, Projective (P.X i) := fun i =>
    have := hproj i
    (P.X i).projective_of_categoryTheory_projective
  have : F.IsKProjective := CochainComplex.isKProjective_of_projective F c
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨h⟩ := CochainComplex.IsKProjective.nonempty_homotopyEquiv_of_iso eF
  refine ⟨F, fun i => Module.finrank (IsLocalRing.ResidueField A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) i).obj
        (D.functor.obj (DerivedCategory.Q.obj P))),
    hX, fun i => ?_, ⟨h⟩⟩
  have := hFc
  have := hFproj
  have hc : IsIso (D.comparison.app F) := D.comparison_isIso_of_projective F c
  let e : D.functor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (fibreComplex (IsLocalRing.residue A) F) :=
    D.functor.mapIso eF.symm ≪≫ @asIso _ _ _ _ (D.comparison.app F) hc
  exact (((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _).toLinearEquiv.finrank_eq).symm

end MinimalModel

section Localization

variable {R : Type u} [CommRing R] {K : Type u} [Field K] (χ : R →+* K)

/-- The kernel of a ring homomorphism to a field is a prime ideal. -/
instance isPrime_ker : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ

/-- The localization of `R` at the kernel of `χ : R ⟶ K`. -/
abbrev Loc : Type u := Localization.AtPrime (RingHom.ker χ)

/-- `χ` extended to the localization at its kernel. -/
def locHom : Loc χ →+* K :=
  IsLocalization.lift (M := (RingHom.ker χ).primeCompl) (S := Loc χ) (g := χ)
    (fun s => isUnit_iff_ne_zero.2 fun h => s.2 (RingHom.mem_ker.2 h))

/-- `locHom χ` composed with the localization map `R ⟶ R_p` is `χ`. -/
theorem locHom_comp : (locHom χ).comp (algebraMap R (Loc χ)) = χ :=
  IsLocalization.lift_comp _

/-- `locHom χ` sends the image of `r : R` in `R_p` to `χ r`. -/
theorem locHom_algebraMap (r : R) : locHom χ (algebraMap R (Loc χ) r) = χ r :=
  IsLocalization.lift_eq _ r

/-- `locHom χ` is a local homomorphism. -/
instance isLocalHom_locHom : IsLocalHom (locHom χ) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker χ).primeCompl a
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hr
  apply ha.ne_zero
  rw [locHom, IsLocalization.lift_mk', RingHom.mem_ker.1 hr, zero_mul]

/-- `locHom χ` does not kill the image of an element outside the kernel of `χ`. -/
theorem locHom_algebraMap_ne_zero (s : (RingHom.ker χ).primeCompl) :
    locHom χ (algebraMap R (Loc χ) s) ≠ 0 := by
  rw [locHom_algebraMap]
  exact fun h => s.2 (RingHom.mem_ker.2 h)

/-- Extension of scalars along `χ` is extension to the localization followed by extension
along `locHom χ`. -/
def extendScalarsLocIso :
    ModuleCat.extendScalars.{u, u, u} χ ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap R (Loc χ)) ⋙
        ModuleCat.extendScalars.{u, u, u} (locHom χ) :=
  eqToIso (by rw [locHom_comp]) ≪≫ ModuleCat.extendScalarsComp _ _

/-- The fibre of a complex along `χ` is the fibre along `locHom χ` of its localization. -/
def fibreComplexLocIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    fibreComplex χ P ≅ fibreComplex (locHom χ) (fibreComplex (algebraMap R (Loc χ)) P) :=
  (NatIso.mapHomologicalComplex (extendScalarsLocIso χ) (ComplexShape.up ℤ)).app P

/-- The isomorphism `fibreComplexLocIso χ` is natural in the complex. -/
theorem fibreComplexLocIso_hom_naturality {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : P ⟶ P') :
    ((ModuleCat.extendScalars χ).mapHomologicalComplex _).map φ ≫
        (fibreComplexLocIso χ P').hom =
      (fibreComplexLocIso χ P).hom ≫ ((ModuleCat.extendScalars (locHom χ)).mapHomologicalComplex
        _).map (((ModuleCat.extendScalars (algebraMap R (Loc χ))).mapHomologicalComplex _).map φ) :=
  (NatIso.mapHomologicalComplex (extendScalarsLocIso χ) (ComplexShape.up ℤ)).hom.naturality φ

/-- **Clearing denominators.** Every element of the localization `R_p ⊗_R M` has a multiple,
by an element of `R` outside `p`, of the form `1 ⊗ m`. -/
theorem exists_smul_eq_fibreElt (M : ModuleCat.{u} R)
    (c : (ModuleCat.extendScalars (algebraMap R (Loc χ))).obj M) :
    ∃ (s : (RingHom.ker χ).primeCompl) (m : M),
      algebraMap R (Loc χ) s • c = fibreElt (algebraMap R (Loc χ)) M m := by
  induction mem_span_range_fibreElt (algebraMap R (Loc χ)) M c using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨1, m, by rw [Submonoid.coe_one, map_one, one_smul]⟩
  | zero => exact ⟨1, 0, by
      rw [smul_zero]
      exact (TensorProduct.tmul_zero _ _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, m₁, h₁⟩ := hx
    obtain ⟨s₂, m₂, h₂⟩ := hy
    refine ⟨s₁ * s₂, (s₂ : R) • m₁ + (s₁ : R) • m₂, ?_⟩
    rw [fibreElt_add, fibreElt_smul, fibreElt_smul, ← h₁, ← h₂, smul_add, smul_smul, smul_smul,
      Submonoid.coe_mul, map_mul, mul_comm (algebraMap R (Loc χ) s₂)]
  | smul a x _ hx =>
    obtain ⟨s₁, m₁, h₁⟩ := hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker χ).primeCompl a
    refine ⟨s * s₁, r • m₁, ?_⟩
    rw [fibreElt_smul, ← h₁, smul_smul, smul_smul, Submonoid.coe_mul, map_mul]
    congr 1
    dsimp only
    rw [mul_right_comm, IsLocalization.mk'_spec']

/-- **The kernel of localization is torsion.** If `1 ⊗ m` vanishes in `R_p ⊗_R M` then some
element of `R` outside `p` kills `m`. -/
theorem exists_smul_eq_zero_of_fibreElt_eq_zero (M : ModuleCat.{u} R) (m : M)
    (hm : fibreElt (algebraMap R (Loc χ)) M m = 0) :
    ∃ t : (RingHom.ker χ).primeCompl, (t : R) • m = 0 := by
  let e : fibreScalars (algebraMap R (Loc χ)) ≃ₗ[R] Loc χ :=
    { toFun := fun a => a
      invFun := fun a => a
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => (Algebra.smul_def r (show Loc χ from a)).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : TensorProduct.mk R (Loc χ) M 1 m = TensorProduct.mk R (Loc χ) M 1 0 := by
    rw [map_zero]
    exact (congrArg (TensorProduct.map e.toLinearMap (LinearMap.id : M →ₗ[R] M)) hm).trans
      (map_zero _)
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := (RingHom.ker χ).primeCompl) h1
  exact ⟨t, by rwa [smul_zero] at ht⟩

/-- **Clearing denominators of a cycle.** A degree-`0` cycle `c` of the localization of `P` has a
multiple `s • c`, by an element `s` of `R` outside `p`, of the form `1 ⊗ m`, where `t • m` is a
cycle of `P` for some further `t` outside `p`. -/
private theorem exists_smul_eq_fibreElt_of_d_eq_zero {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {c : (ModuleCat.extendScalars (algebraMap R (Loc χ))).obj (P.X 0)}
    (hc : (fibreComplex (algebraMap R (Loc χ)) P).d 0 1 c = 0) :
    ∃ (s t : (RingHom.ker χ).primeCompl) (m : P.X 0),
      algebraMap R (Loc χ) s • c = fibreElt (algebraMap R (Loc χ)) _ m ∧
        P.d 0 1 ((t : R) • m) = 0 := by
  obtain ⟨s, m, hsm⟩ := exists_smul_eq_fibreElt χ (P.X 0) c
  have hdm : fibreElt (algebraMap R (Loc χ)) _ (P.d 0 1 m) = 0 := by
    change (fibreComplex (algebraMap R (Loc χ)) P).d 0 1 (fibreElt (algebraMap R (Loc χ)) _ m) = 0
    rw [← hsm, map_smul, hc, smul_zero]
  obtain ⟨t, ht⟩ := exists_smul_eq_zero_of_fibreElt_eq_zero χ (P.X 1) _ hdm
  exact ⟨s, t, m, hsm, by rwa [map_smul]⟩

/-- A map whose fibre along `locHom χ` of its localization is nonzero on cohomology in some
degree has fibre along `χ` nonzero on cohomology in that degree. -/
private theorem homologyMap_fibreMap_ne_zero_of_locHom {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (y : P ⟶ P') (i : ℤ) (h : HomologicalComplex.homologyMap
      (fibreMap (locHom χ) (fibreMap (algebraMap R (Loc χ)) y)) i ≠ 0) :
    HomologicalComplex.homologyMap (fibreMap χ y) i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun ψ => HomologicalComplex.homologyMap ψ i)
    (fibreComplexLocIso_hom_naturality χ y)
  simp only [HomologicalComplex.homologyMap_comp, h0, zero_comp] at this
  rw [← cancel_epi (HomologicalComplex.homologyMap (fibreComplexLocIso χ P).hom i), comp_zero]
  exact this.symm

end Localization

section Unit

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] (f : A →+* S)

/-- A complex concentrated in degree `0` whose degree-`0` term is generated by one element. -/
structure IsCyclicInDegreeZero (U : CochainComplex (ModuleCat.{u} A) ℤ) (g : U.X 0) : Prop where
  isZero : ∀ i, i ≠ 0 → IsZero (U.X i)
  generates : ∀ m : U.X 0, ∃ a : A, m = a • g

/-- The unit complex `A` in degree `0`. -/
abbrev unitComplex (A : Type u) [CommRing A] : CochainComplex (ModuleCat.{u} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A)

/-- The generator `1` of the unit complex in degree `0`. -/
def unitGen (A : Type u) [CommRing A] : (unitComplex A).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv (1 : A)

/-- The unit complex `A` in degree `0` is generated by `1`. -/
theorem isCyclicInDegreeZero_unitComplex :
    IsCyclicInDegreeZero (unitComplex A) (unitGen A) where
  isZero i hi := HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  generates m := by
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
    refine ⟨e.hom m, ?_⟩
    have h1 : m = e.inv (e.hom m) := by
      change m = (e.hom ≫ e.inv) m
      rw [e.hom_inv_id]
      rfl
    conv_lhs => rw [h1]
    have h2 : e.inv (e.hom m) = e.hom m • e.inv (1 : A) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    exact h2

/-- If `U` is concentrated in degree `0` and generated by `g`, then its fibre along `f` is
concentrated in degree `0` and generated by `1 ⊗ g`. -/
theorem IsCyclicInDegreeZero.fibre {U : CochainComplex (ModuleCat.{u} A) ℤ} {g : U.X 0}
    (hU : IsCyclicInDegreeZero U g) :
    IsCyclicInDegreeZero (fibreComplex f U) (fibreElt f _ g) where
  isZero i hi := (ModuleCat.extendScalars f).map_isZero (hU.isZero i hi)
  generates x := by
    have hsub : (Submodule.span S (Set.range (fibreElt f (U.X 0))) :
        Submodule S ((ModuleCat.extendScalars f).obj (U.X 0))) ≤
        Submodule.span S {fibreElt f (U.X 0) g} := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      obtain ⟨a, rfl⟩ := hU.generates m
      rw [fibreElt_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hsub (mem_span_range_fibreElt f _ x))
    exact ⟨s, hs.symm⟩

/-- Maps out of a complex concentrated in degree `0` with cyclic degree-`0` term are determined
by the image of the generator. -/
theorem IsCyclicInDegreeZero.hom_ext {U : CochainComplex (ModuleCat.{u} A) ℤ} {g : U.X 0}
    (hU : IsCyclicInDegreeZero U g) {C : CochainComplex (ModuleCat.{u} A) ℤ} {φ ψ : U ⟶ C}
    (h : φ.f 0 g = ψ.f 0 g) : φ = ψ := by
  ext i x
  by_cases hi : i = 0
  · subst hi
    obtain ⟨a, rfl⟩ := hU.generates x
    rw [map_smul, map_smul, h]
  · exact congrArg (fun χ => χ x) ((hU.isZero i hi).eq_of_src (φ.f i) (ψ.f i))

/-- The terms of the unit complex are projective. -/
private theorem projective_unitComplex_X (i : ℤ) : Projective ((unitComplex A).X i) := by
  by_cases hi : i = 0
  · subst hi
    exact Projective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of A A)).symm inferInstance
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).projective

/-- The unit complex is concentrated in degrees at most `0`. -/
private theorem isStrictlyLE_unitComplex : (unitComplex A).IsStrictlyLE 0 := by
  change ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)).IsStrictlyLE 0
  infer_instance

/-- A degree-`0` cycle `x` of a complex is the image of the generator under a map from the unit
complex. -/
private theorem exists_unitComplex_hom_f_unitGen {P : CochainComplex (ModuleCat.{u} A) ℤ}
    {x : P.X 0} (hx : P.d 0 1 x = 0) : ∃ y : unitComplex A ⟶ P, y.f 0 (unitGen A) = x := by
  let y : unitComplex A ⟶ P := HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (LinearMap.toSpanSingleton A (P.X 0) x)) (fun j hj => by
      obtain rfl : j = 1 := by simpa using hj.symm
      ext
      simp [LinearMap.toSpanSingleton_apply, hx])
  refine ⟨y, ?_⟩
  rw [HomologicalComplex.mkHomFromSingle_f]
  change (LinearMap.toSpanSingleton A (P.X 0) x)
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv 1)) = x
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  exact one_smul A x

end Unit

section LocalModel

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {K : Type u} [Field K] (χ : R →+* K)

/-- The localization at `ker χ` of a bounded complex of finite projective `R`-modules is homotopy
equivalent to a complex of finite free modules whose fibre along `locHom χ` has zero
differentials. -/
theorem exists_local_minimal_model (C : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite R (C.X i)) (hproj : ∀ i, Module.Projective R (C.X i)) :
    ∃ (F : CochainComplex (ModuleCat.{u} (Loc χ)) ℤ) (r : ℤ → ℕ),
      (∀ i, Nonempty (F.X i ≅ ModuleCat.of (Loc χ) (ULift.{u} (Fin (r i) → Loc χ)))) ∧
      (∀ i j, (fibreComplex (locHom χ) F).d i j = 0) ∧
      Nonempty (HomotopyEquiv F (fibreComplex (algebraMap R (Loc χ)) C)) := by
  let α := algebraMap R (Loc χ)
  have hGE : (fibreComplex α C).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      (ModuleCat.extendScalars α).map_isZero (C.isZero_of_isStrictlyGE a i hi)
  have hLE : (fibreComplex α C).IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      (ModuleCat.extendScalars α).map_isZero (C.isZero_of_isStrictlyLE b i hi)
  have hfin' : ∀ i, Module.Finite (Loc χ) ((fibreComplex α C).X i) := fun i =>
    have := hfin i
    Stacks.DerivedTensorHomDiagonal.finite_extendScalars α (C.X i)
  have hproj' : ∀ i, Module.Projective (Loc χ) ((fibreComplex α C).X i) := fun i =>
    have := hproj i
    have : Projective ((ModuleCat.extendScalars α).obj (C.X i)) :=
      (ModuleCat.extendRestrictScalarsAdj α).map_projective (C.X i) inferInstance
    ((ModuleCat.extendScalars α).obj (C.X i)).projective_of_module_projective
  obtain ⟨F, r, hX, hH, ⟨h⟩⟩ := exists_minimal_model (fibreComplex α C) a b hfin' hproj'
  exact ⟨F, r, hX, fibreComplex_d_eq_zero (locHom χ) F r hX hH, ⟨h⟩⟩

/-- A complex concentrated in degree `0` has zero differentials. -/
theorem d_eq_zero_of_isCyclicInDegreeZero {A : Type u} [CommRing A]
    {U : CochainComplex (ModuleCat.{u} A) ℤ} {g : U.X 0} (hU : IsCyclicInDegreeZero U g)
    (i j : ℤ) : U.d i j = 0 := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst hi hj
      exact U.shape _ _ (by simp)
    · exact (hU.isZero j hj).eq_of_tgt _ _
  · exact (hU.isZero i hi).eq_of_src _ _

/-- A map of complexes whose homology map is zero in some degree after composing with an
isomorphism on either side had zero homology map. -/
theorem homologyMap_ne_zero_of_comp {C : Type*} [Category C] [Abelian C]
    {X Y Z : CochainComplex C ℤ} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (i : ℤ)
    (h : HomologicalComplex.homologyMap (φ ≫ ψ) i ≠ 0) :
    HomologicalComplex.homologyMap φ i ≠ 0 := by
  intro h0
  apply h
  rw [HomologicalComplex.homologyMap_comp, h0, zero_comp]

end LocalModel

section Main

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {K : Type u} [Field K] (χ : R →+* K)

/-- The unit complex is K-projective. -/
private local instance isKProjective_unitComplex : (unitComplex R).IsKProjective :=
  have := projective_unitComplex_X (A := R)
  have := isStrictlyLE_unitComplex (A := R)
  CochainComplex.isKProjective_of_projective _ 0

/-- A complex over `R_p` whose fibre along `locHom χ` has zero differentials and which is
homotopy equivalent to the localization of `Q` has terms of rank the dimension of the
cohomology of `K ⊗ Q`. -/
private theorem finrank_X_eq_finrank_fibre_homology {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {G : CochainComplex (ModuleCat.{u} (Loc χ)) ℤ} {i : ℤ} {r : ℕ}
    (e : G.X i ≅ ModuleCat.of (Loc χ) (ULift.{u} (Fin r → Loc χ)))
    (hGmin : ∀ i j, (fibreComplex (locHom χ) G).d i j = 0)
    (hG : HomotopyEquiv G (fibreComplex (algebraMap R (Loc χ)) Q)) :
    Module.finrank (Loc χ) (G.X i) = Module.finrank K ((fibreComplex χ Q).homology i) := by
  have e1 : Module.finrank (Loc χ) (G.X i) = r := by
    rw [e.toLinearEquiv.finrank_eq, ULift.moduleEquiv.finrank_eq, Module.finrank_fin_fun]
  have e2 : Module.finrank K ((fibreComplex (locHom χ) G).X i) = r :=
    (finrank_fibre_ulift (locHom χ) r (G.X i) e).1
  have e3 : Module.finrank K ((fibreComplex (locHom χ) G).X i) =
      Module.finrank K ((fibreComplex (locHom χ) G).homology i) :=
    (zeroDiffHomologyIso (fibreComplex (locHom χ) G) hGmin i).toLinearEquiv.finrank_eq
  have e4 : Module.finrank K ((fibreComplex (locHom χ) G).homology i) =
      Module.finrank K
        ((fibreComplex (locHom χ) (fibreComplex (algebraMap R (Loc χ)) Q)).homology i) :=
    (((ModuleCat.extendScalars (locHom χ)).mapHomotopyEquiv hG
      (c := ComplexShape.up ℤ)).toHomologyIso i).toLinearEquiv.finrank_eq
  have e5 : Module.finrank K ((fibreComplex χ Q).homology i) =
      Module.finrank K
        ((fibreComplex (locHom χ) (fibreComplex (algebraMap R (Loc χ)) Q)).homology i) :=
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (fibreComplexLocIso χ Q)).toLinearEquiv.finrank_eq
  omega

/-- A map `R[0] ⟶ Q` with nonzero fibre in `D(K)` gives a degree-`0` cycle of nonzero fibre in
any complex over `R_p` homotopy equivalent to the localization of `Q`. -/
private theorem exists_cycle_fibreElt_ne_zero {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {G : CochainComplex (ModuleCat.{u} (Loc χ)) ℤ}
    (hG : HomotopyEquiv G (fibreComplex (algebraMap R (Loc χ)) Q))
    (hz : ∃ z : unitComplex R ⟶ Q, DerivedCategory.Q.map (fibreMap χ z) ≠ 0) :
    ∃ z : G.X 0, G.d 0 1 z = 0 ∧ fibreElt (locHom χ) _ z ≠ 0 := by
  obtain ⟨zR, hzR⟩ := hz
  let α := algebraMap R (Loc χ)
  let χA := locHom χ
  -- the unit complex and its fibres
  have hU := isCyclicInDegreeZero_unitComplex (A := R)
  have hUA := hU.fibre α
  have hUK := hUA.fibre χA
  let eG := (ModuleCat.extendScalars χA).mapHomotopyEquiv hG (c := ComplexShape.up ℤ)
  let w : fibreComplex α (unitComplex R) ⟶ G := fibreMap α zR ≫ hG.inv
  refine ⟨w.f 0 (fibreElt α _ (unitGen R)), ?_, ?_⟩
  · have hc := w.comm 0 1
    rw [d_eq_zero_of_isCyclicInDegreeZero hUA, zero_comp] at hc
    exact (congrArg (fun φ => φ.hom (fibreElt α _ (unitGen R))) hc).trans rfl
  · intro hzero
    have hw : fibreMap χA w = 0 := by
      refine hUK.hom_ext ?_
      change fibreElt χA _ (w.f 0 (fibreElt α _ (unitGen R))) = 0
      exact hzero
    have hw' : fibreMap χA (fibreMap α zR) ≫ eG.inv = 0 := by
      rw [← hw]
      exact (Functor.map_comp _ _ _).symm
    have hQiso : IsIso (DerivedCategory.Q.map eG.inv) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} K) _).2 inferInstance
    have h0 : DerivedCategory.Q.map (fibreMap χA (fibreMap α zR)) = 0 := by
      rw [← cancel_mono (DerivedCategory.Q.map eG.inv), ← Functor.map_comp, hw',
        Functor.map_zero, zero_comp]
    apply hzR
    rw [← cancel_mono (DerivedCategory.Q.map (fibreComplexLocIso χ Q).hom), ← Functor.map_comp,
      fibreComplexLocIso_hom_naturality, Functor.map_comp, h0, comp_zero, zero_comp]

/-- Joint injectivity of the maps `H¹(K ⊗ ψ k)` gives joint injectivity, in degree `1`, of the
fibres of the induced maps between complexes over `R_p` with minimal fibres homotopy equivalent
to the localizations. -/
private theorem eq_zero_of_fibre_map_eq_zero_of_homotopyEquiv
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {ι : Type u}
    {Q : ι → CochainComplex (ModuleCat.{u} R) ℤ} (ψ : ∀ k, P ⟶ Q k)
    {F : CochainComplex (ModuleCat.{u} (Loc χ)) ℤ}
    {G : ι → CochainComplex (ModuleCat.{u} (Loc χ)) ℤ}
    (hF : HomotopyEquiv F (fibreComplex (algebraMap R (Loc χ)) P))
    (hG : ∀ k, HomotopyEquiv (G k) (fibreComplex (algebraMap R (Loc χ)) (Q k)))
    (hFmin : ∀ i j, (fibreComplex (locHom χ) F).d i j = 0)
    (hGmin : ∀ k i j, (fibreComplex (locHom χ) (G k)).d i j = 0)
    (h1 : ∀ c : (fibreComplex χ P).homology 1,
      (∀ k, HomologicalComplex.homologyMap (fibreMap χ (ψ k)) 1 c = 0) → c = 0)
    (x : (fibreComplex (locHom χ) F).X 1)
    (hx : ∀ k, (ModuleCat.extendScalars (locHom χ)).map
      ((hF.hom ≫ fibreMap (algebraMap R (Loc χ)) (ψ k) ≫ (hG k).inv).f 1) x = 0) :
    x = 0 := by
  let α := algebraMap R (Loc χ)
  let χA := locHom χ
  let θ : ∀ k, F ⟶ G k := fun k => hF.hom ≫ fibreMap α (ψ k) ≫ (hG k).inv
  have hx' : ∀ k, (ModuleCat.extendScalars χA).map ((θ k).f 1) x = 0 := hx
  let eF := (ModuleCat.extendScalars χA).mapHomotopyEquiv hF (c := ComplexShape.up ℤ)
  let eG := fun k => (ModuleCat.extendScalars χA).mapHomotopyEquiv (hG k) (c := ComplexShape.up ℤ)
  let zF := zeroDiffHomologyIso (fibreComplex χA F) hFmin
  let zG := fun k => zeroDiffHomologyIso (fibreComplex χA (G k)) (hGmin k)
  let εP := fibreComplexLocIso χ P
  let εQ := fun k => fibreComplexLocIso χ (Q k)
  have hεψ : ∀ k, (HomologicalComplex.homologyMap εP.inv 1) ≫
      HomologicalComplex.homologyMap (fibreMap χ (ψ k)) 1 =
      HomologicalComplex.homologyMap (fibreMap χA (fibreMap α (ψ k))) 1 ≫
        HomologicalComplex.homologyMap (εQ k).inv 1 := by
    intro k
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact fibreComplexLocIso_hom_naturality χ (ψ k)
  let c := (zF 1).hom x
  have hk : ∀ k, HomologicalComplex.homologyMap (fibreMap χ (ψ k)) 1
      (HomologicalComplex.homologyMap εP.inv 1
        (HomologicalComplex.homologyMap eF.hom 1 c)) = 0 := by
    intro k
    have hθ : fibreMap χA (θ k) =
        eF.hom ≫ fibreMap χA (fibreMap α (ψ k)) ≫ (eG k).inv := by
      simp only [θ, Functor.map_comp]
      rfl
    have h2 : HomologicalComplex.homologyMap (fibreMap χA (θ k)) 1 c = 0 := by
      have := congrArg (fun φ => φ.hom x)
        (zeroDiffHomologyIso_hom_naturality hFmin (hGmin k) (fibreMap χA (θ k)) 1)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      change (zG k 1).hom ((ModuleCat.extendScalars χA).map ((θ k).f 1) x) = 0
      rw [hx' k, map_zero]
    rw [hθ, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h2
    have h3 : HomologicalComplex.homologyMap (fibreMap χA (fibreMap α (ψ k))) 1
        (HomologicalComplex.homologyMap eF.hom 1 c) = 0 :=
      eq_zero_of_iso_hom_apply_eq_zero ((eG k).symm.toHomologyIso 1) h2
    have := congrArg (fun φ => φ.hom (HomologicalComplex.homologyMap eF.hom 1 c)) (hεψ k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, h3, map_zero]
  have hc' := eq_zero_of_iso_hom_apply_eq_zero
    ((HomologicalComplex.homologyFunctor _ _ 1).mapIso εP.symm) (h1 _ hk)
  exact eq_zero_of_iso_hom_apply_eq_zero (zF 1)
    (eq_zero_of_iso_hom_apply_eq_zero (eF.toHomologyIso 1) hc')

/-- **Lifting a cycle of a minimal model.** Let `F` be a complex over `R_p` homotopy equivalent
to the localization of `P`, whose fibre along `locHom χ` has zero differentials and with
`d⁰ = 0`. A degree-`0` element of `F` with nonzero fibre gives a map `R[0] ⟶ P` whose localized
fibre is nonzero on `H⁰`. -/
private theorem exists_unit_map_loc_homologyMap_ne_zero {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {F : CochainComplex (ModuleCat.{u} (Loc χ)) ℤ}
    (hF : HomotopyEquiv F (fibreComplex (algebraMap R (Loc χ)) P))
    (hFmin : ∀ i j, (fibreComplex (locHom χ) F).d i j = 0) (hd : F.d 0 1 = 0) {e : F.X 0}
    (he : fibreElt (locHom χ) _ e ≠ 0) :
    ∃ y : unitComplex R ⟶ P, HomologicalComplex.homologyMap
      (fibreMap (locHom χ) (fibreMap (algebraMap R (Loc χ)) y)) 0 ≠ 0 := by
  let α := algebraMap R (Loc χ)
  let χA := locHom χ
  let c : (fibreComplex α P).X 0 := hF.hom.f 0 e
  have hdc : (fibreComplex α P).d 0 1 c = 0 := by
    have := congrArg (fun φ => φ.hom e) (hF.hom.comm 0 1)
    rwa [hd, zero_comp] at this
  -- Step 6: clear denominators
  obtain ⟨s, t, m, hsm, hdx⟩ := exists_smul_eq_fibreElt_of_d_eq_zero χ hdc
  obtain ⟨y, hy⟩ := exists_unitComplex_hom_f_unitGen hdx
  refine ⟨y, ?_⟩
  -- Step 7: the class of `t • m` in the fibre is nonzero
  -- the fibre of `hF.hom ≫ hF.inv` is the identity in degree zero
  have hid := fibreMap_homotopyEquiv_hom_inv_f χA hF hFmin 0
  let gen := fibreElt χA _ (fibreElt α _ (unitGen R))
  let φ := fibreMap χA (fibreMap α y ≫ hF.inv)
  have hφ : φ.f 0 gen = (χ t * χ s) • fibreElt χA _ e := by
    change fibreElt χA _ (hF.inv.f 0 (fibreElt α _ (y.f 0 (unitGen R)))) = _
    rw [hy, fibreElt_smul, ← hsm, smul_smul, map_smul, fibreElt_smul]
    have h2 : fibreElt χA _ (hF.inv.f 0 c) = fibreElt χA _ e :=
      congrArg (fun ψ => ψ.hom (fibreElt χA _ e)) hid
    rw [h2, map_mul, locHom_algebraMap, locHom_algebraMap]
  have hφne : φ.f 0 gen ≠ 0 := by
    rw [hφ]
    refine smul_ne_zero (mul_ne_zero ?_ ?_) he
    · exact fun h => t.2 (RingHom.mem_ker.2 h)
    · exact fun h => s.2 (RingHom.mem_ker.2 h)
  have hUK := ((isCyclicInDegreeZero_unitComplex (A := R)).fibre α).fibre χA
  have hHφ : HomologicalComplex.homologyMap φ 0 ≠ 0 :=
    homologyMap_ne_zero_of_f_ne_zero (d_eq_zero_of_isCyclicInDegreeZero hUK) hFmin φ 0
      fun hf => hφne (by rw [hf]; rfl)
  exact homologyMap_ne_zero_of_comp _ (fibreMap χA hF.inv) 0 (by rwa [← Functor.map_comp])

/-- **The matrix argument of [Stacks, Tag 0BF2], for complexes.** Let `P` and `Q k` (`k` in a
finite type) be bounded complexes of finite projective `R`-modules, let `ψ k : P ⟶ Q k` be maps
of complexes and let `χ : R ⟶ K` be a homomorphism to a field. Suppose that
* the maps `H¹(K ⊗ ψ k)` are jointly injective;
* each `H⁰(K ⊗ Q k)` has dimension at most one and is reached by a degree-`0` cycle of `Q k`
  (a map `R[0] ⟶ Q k` whose fibre is nonzero in `D(K)`);
* `H⁰(K ⊗ P) ≠ 0`.
Then some degree-`0` cycle of `P` has nonzero class in `H⁰(K ⊗ P)`. -/
theorem exists_unit_map_homologyMap_ne_zero
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (aP bP : ℤ) [P.IsStrictlyGE aP] [P.IsStrictlyLE bP]
    (hPfin : ∀ i, Module.Finite R (P.X i)) (hPproj : ∀ i, Module.Projective R (P.X i))
    {ι : Type u} [Finite ι] (Q : ι → CochainComplex (ModuleCat.{u} R) ℤ) (aQ bQ : ι → ℤ)
    [∀ k, (Q k).IsStrictlyGE (aQ k)] [∀ k, (Q k).IsStrictlyLE (bQ k)]
    (hQfin : ∀ k i, Module.Finite R ((Q k).X i))
    (hQproj : ∀ k i, Module.Projective R ((Q k).X i))
    (ψ : ∀ k, P ⟶ Q k)
    (h1 : ∀ c : (fibreComplex χ P).homology 1,
      (∀ k, HomologicalComplex.homologyMap (fibreMap χ (ψ k)) 1 c = 0) → c = 0)
    (hdim : ∀ k, Module.finrank K ((fibreComplex χ (Q k)).homology 0) ≤ 1)
    (hz : ∀ k, ∃ z : unitComplex R ⟶ Q k, DerivedCategory.Q.map (fibreMap χ z) ≠ 0)
    (hne : Nontrivial ((fibreComplex χ P).homology 0)) :
    ∃ y : unitComplex R ⟶ P, HomologicalComplex.homologyMap (fibreMap χ y) 0 ≠ 0 := by
  classical
  let α := algebraMap R (Loc χ)
  let χA := locHom χ
  obtain ⟨F, r, hFX, hFmin, ⟨hF⟩⟩ := exists_local_minimal_model χ P aP bP hPfin hPproj
  choose G rG hGX hGmin hG using fun k =>
    exists_local_minimal_model χ (Q k) (aQ k) (bQ k) (hQfin k) (hQproj k)
  have hFfree : ∀ i, Module.Free (Loc χ) (F.X i) := fun i =>
    Module.Free.of_equiv (hFX i).some.toLinearEquiv.symm
  have hFfin : ∀ i, Module.Finite (Loc χ) (F.X i) := fun i =>
    Module.Finite.equiv (hFX i).some.toLinearEquiv.symm
  have hGfree : ∀ k i, Module.Free (Loc χ) ((G k).X i) := fun k i =>
    Module.Free.of_equiv (hGX k i).some.toLinearEquiv.symm
  have hGfin : ∀ k i, Module.Finite (Loc χ) ((G k).X i) := fun k i =>
    Module.Finite.equiv (hGX k i).some.toLinearEquiv.symm
  let hG' : ∀ k, HomotopyEquiv (G k) (fibreComplex α (Q k)) := fun k => (hG k).some
  -- the localized maps
  let θ : ∀ k, F ⟶ G k := fun k => hF.hom ≫ fibreMap α (ψ k) ≫ (hG' k).inv
  -- the homotopy equivalences after the fibre
  let eF := (ModuleCat.extendScalars χA).mapHomotopyEquiv hF (c := ComplexShape.up ℤ)
  -- the zero-differential identifications
  let zF := zeroDiffHomologyIso (fibreComplex χA F) hFmin
  let εP := fibreComplexLocIso χ P
  -- Step 4: the differential `F⁰ ⟶ F¹` vanishes
  have hd : F.d 0 1 = 0 := d_zero_one_eq_zero χA F G θ
    -- Step 3: joint injectivity in degree one, on the minimal models
    (eq_zero_of_fibre_map_eq_zero_of_homotopyEquiv χ ψ hF hG' hFmin hGmin h1)
    -- Step 1: ranks of the degree-zero terms of the `G k`
    (fun k => (finrank_X_eq_finrank_fibre_homology χ (hGX k 0).some (hGmin k) (hG' k)).trans_le
      (hdim k))
    -- Step 2: each `G k` has a degree-zero cycle of nonzero fibre
    (fun k => exists_cycle_fibreElt_ne_zero χ (hG' k) (hz k))
  -- Step 5: a degree-zero element of `F` with nonzero fibre
  obtain ⟨e, he⟩ : ∃ e : F.X 0, fibreElt χA _ e ≠ 0 := by
    let E : (fibreComplex χ P).homology 0 ≅ (fibreComplex χA F).X 0 :=
      (HomologicalComplex.homologyFunctor _ _ 0).mapIso εP ≪≫
        (eF.toHomologyIso 0).symm ≪≫ (zF 0).symm
    have : Nontrivial ((ModuleCat.extendScalars χA).obj (F.X 0)) :=
      E.toLinearEquiv.injective.nontrivial
    exact exists_fibreElt_ne_zero χA (F.X 0)
  -- Steps 6 and 7: clear denominators; the class of the resulting cycle in the fibre is nonzero
  obtain ⟨y, hy⟩ := exists_unit_map_loc_homologyMap_ne_zero χ hF hFmin hd he
  exact ⟨y, homologyMap_fibreMap_ne_zero_of_locHom χ y 0 hy⟩

open CochainComplex.DerivedExtensionScalars in
/-- A map `R[0] ⟶ N` with nonzero derived fibre lifts to a map `R[0] ⟶ X` of complexes with
nonzero fibre in `D(K)`, for any complex `X` representing `N` on which the comparison of `D` is
an isomorphism. -/
private theorem exists_fibreMap_ne_zero_of_functor_map_ne_zero
    (D : TotalDerivedExtensionScalars.{u, u, u} χ) {N : DerivedCategory (ModuleCat.{u} R)}
    {X : CochainComplex (ModuleCat.{u} R) ℤ} (e : N ≅ DerivedCategory.Q.obj X)
    (hX : IsIso (D.comparison.app X))
    (hz : ∃ z : DerivedCategory.Q.obj (unitComplex R) ⟶ N, D.functor.map z ≠ 0) :
    ∃ z : unitComplex R ⟶ X, DerivedCategory.Q.map (fibreMap χ z) ≠ 0 := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨zt, hzt⟩ := CochainComplex.IsKProjective.Q_map_surjective (unitComplex R) X (z ≫ e.hom)
  refine ⟨zt, fun h0 => hz ?_⟩
  let c : ∀ W : CochainComplex (ModuleCat.{u} R) ℤ,
      D.functor.obj (DerivedCategory.Q.obj W) ⟶ DerivedCategory.Q.obj (fibreComplex χ W) :=
    fun W => D.comparison.app W
  have : Mono (c X) := (inferInstance : Mono (D.comparison.app X))
  have hn : D.functor.map (DerivedCategory.Q.map zt) ≫ c X =
      c (unitComplex R) ≫ DerivedCategory.Q.map (fibreMap χ zt) :=
    D.comparison.naturality zt
  rw [h0, comp_zero, hzt, Functor.map_comp, Category.assoc] at hn
  rw [← cancel_mono (D.functor.map e.hom), zero_comp, ← cancel_mono (c X), zero_comp,
    Category.assoc]
  exact hn

open CochainComplex.DerivedExtensionScalars in
/-- A map of complexes `X ⟶ Y`, with the comparison of `D` an isomorphism on `X`, whose fibre is
nonzero on cohomology in some degree has nonzero derived fibre. -/
private theorem functor_map_Q_map_ne_zero (D : TotalDerivedExtensionScalars.{u, u, u} χ)
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (φ : X ⟶ Y) (hX : IsIso (D.comparison.app X))
    (i : ℤ) (h : HomologicalComplex.homologyMap (fibreMap χ φ) i ≠ 0) :
    D.functor.map (DerivedCategory.Q.map φ) ≠ 0 := by
  intro h0
  apply h
  let c : ∀ W : CochainComplex (ModuleCat.{u} R) ℤ,
      D.functor.obj (DerivedCategory.Q.obj W) ⟶ DerivedCategory.Q.obj (fibreComplex χ W) :=
    fun W => D.comparison.app W
  have : Epi (c X) := (inferInstance : Epi (D.comparison.app X))
  have hn : D.functor.map (DerivedCategory.Q.map φ) ≫ c Y =
      c X ≫ DerivedCategory.Q.map (fibreMap χ φ) :=
    D.comparison.naturality φ
  rw [h0, zero_comp] at hn
  have hQ0 : DerivedCategory.Q.map (fibreMap χ φ) = 0 := by
    rw [← cancel_epi (c X), comp_zero]
    exact hn.symm
  have h2 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} K) i).hom.naturality
    (fibreMap χ φ)
  have h3 : (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).map
      (fibreMap χ φ) = 0 := by
    simp only [Functor.comp_map, hQ0, Functor.map_zero]
  rw [h3, zero_comp] at h2
  exact (cancel_epi ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} K) i).hom.app
    (fibreComplex χ X))).1 (h2.symm.trans comp_zero.symm)

open CochainComplex.DerivedExtensionScalars in
/-- **The matrix argument of [Stacks, Tag 0BF2], in the derived category.** Let `M` and `N k`
(`k` in a finite type) be perfect objects of `D(R)`, let `ψ k : M ⟶ N k` and let `χ : R ⟶ K` be a
homomorphism to a field, with derived extension of scalars `D`. Suppose that the maps
`H¹(D ψ k)` are jointly injective, that each `H⁰(D (N k))` has dimension at most one and is
reached by a map `R[0] ⟶ N k` with nonzero fibre, and that `H⁰(D M) ≠ 0`. Then some map
`R[0] ⟶ M` has nonzero fibre. -/
theorem exists_unit_map_derived_ne_zero (D : TotalDerivedExtensionScalars.{u, u, u} χ)
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : StacksDraft.Perfect.IsPerfect M)
    {ι : Type u} [Finite ι] (N : ι → DerivedCategory (ModuleCat.{u} R))
    (hN : ∀ k, StacksDraft.Perfect.IsPerfect (N k)) (ψ : ∀ k, M ⟶ N k)
    (h1 : ∀ c : (DerivedCategory.homologyFunctor (ModuleCat.{u} K) 1).obj (D.functor.obj M),
      (∀ k, (DerivedCategory.homologyFunctor (ModuleCat.{u} K) 1).map (D.functor.map (ψ k)) c = 0) →
        c = 0)
    (hdim : ∀ k, Module.finrank K
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) 0).obj (D.functor.obj (N k))) ≤ 1)
    (hz : ∀ k, ∃ z : DerivedCategory.Q.obj (unitComplex R) ⟶ N k, D.functor.map z ≠ 0)
    (hne : Nontrivial
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) 0).obj (D.functor.obj M))) :
    ∃ y : DerivedCategory.Q.obj (unitComplex R) ⟶ M, D.functor.map y ≠ 0 := by
  classical
  obtain ⟨P, aP, bP, hPge, hPle, hPfin, hPproj, ⟨eM⟩⟩ := hM
  choose Pk aQ bQ hQge hQle hQfin hQproj eN' using hN
  let eN : ∀ k, N k ≅ DerivedCategory.Q.obj (Pk k) := fun k => (eN' k).some
  have hPpr : ∀ i, Projective (P.X i) := fun i =>
    have := hPproj i
    (P.X i).projective_of_categoryTheory_projective
  have hQpr : ∀ k i, Projective ((Pk k).X i) := fun k i =>
    have := hQproj k i
    ((Pk k).X i).projective_of_categoryTheory_projective
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P bP
  -- the comparison isomorphisms
  have hτ : ∀ (X : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [X.IsStrictlyLE b]
      [∀ i, Projective (X.X i)], IsIso (D.comparison.app X) := fun X b _ _ =>
    D.comparison_isIso_of_projective X b
  let τ : ∀ (X : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [X.IsStrictlyLE b]
      [∀ i, Projective (X.X i)],
      D.functor.obj (DerivedCategory.Q.obj X) ≅ DerivedCategory.Q.obj (fibreComplex χ X) :=
    fun X b _ _ => @asIso _ _ _ _ (D.comparison.app X) (hτ X b)
  have hτnat : ∀ (X Y : CochainComplex (ModuleCat.{u} R) ℤ) (b c : ℤ) [X.IsStrictlyLE b]
      [∀ i, Projective (X.X i)] [Y.IsStrictlyLE c] [∀ i, Projective (Y.X i)] (φ : X ⟶ Y),
      D.functor.map (DerivedCategory.Q.map φ) ≫ (τ Y c).hom =
        (τ X b).hom ≫ DerivedCategory.Q.map (fibreMap χ φ) := fun X Y b c _ _ _ _ φ =>
    D.comparison.naturality φ
  -- the chain maps
  have hlift : ∀ k, ∃ ψt : P ⟶ Pk k,
      DerivedCategory.Q.map ψt = eM.inv ≫ ψ k ≫ (eN k).hom := fun k =>
    CochainComplex.IsKProjective.Q_map_surjective P (Pk k) _
  choose ψt hψt using hlift
  -- the cohomology identifications
  let ιM : ∀ n, (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).obj (D.functor.obj M) ≅
      (fibreComplex χ P).homology n := fun n =>
    (DerivedCategory.homologyFunctor _ n).mapIso (D.functor.mapIso eM ≪≫ τ P bP) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _
  let ιN : ∀ k n, (DerivedCategory.homologyFunctor (ModuleCat.{u} K) n).obj
      (D.functor.obj (N k)) ≅ (fibreComplex χ (Pk k)).homology n := fun k n =>
    (DerivedCategory.homologyFunctor _ n).mapIso (D.functor.mapIso (eN k) ≪≫ τ (Pk k) (bQ k)) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _
  have hιψ : ∀ k n, (ιM n).hom ≫ HomologicalComplex.homologyMap (fibreMap χ (ψt k)) n =
      (DerivedCategory.homologyFunctor _ n).map (D.functor.map (ψ k)) ≫ (ιN k n).hom := by
    intro k n
    have h1 : D.functor.map (ψ k) ≫ (D.functor.mapIso (eN k) ≪≫ τ (Pk k) (bQ k)).hom =
        (D.functor.mapIso eM ≪≫ τ P bP).hom ≫ DerivedCategory.Q.map (fibreMap χ (ψt k)) := by
      simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [← hτnat P (Pk k) bP (bQ k), ← Functor.map_comp_assoc, hψt, ← Functor.map_comp_assoc]
      simp
    have h2 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} K) n).hom.naturality
      (fibreMap χ (ψt k))
    change (DerivedCategory.homologyFunctor _ n).map (D.functor.mapIso eM ≪≫ τ P bP).hom ≫
        (DerivedCategory.homologyFunctorFactors _ n).hom.app _ ≫
          HomologicalComplex.homologyMap (fibreMap χ (ψt k)) n =
      (DerivedCategory.homologyFunctor _ n).map (D.functor.map (ψ k)) ≫
        (DerivedCategory.homologyFunctor _ n).map (D.functor.mapIso (eN k) ≪≫ τ (Pk k) (bQ k)).hom ≫
          (DerivedCategory.homologyFunctorFactors _ n).hom.app _
    rw [← Functor.map_comp_assoc, h1, Functor.map_comp, Category.assoc]
    congr 1
    exact h2.symm
  -- the hypotheses of the complex version
  have h1c : ∀ c : (fibreComplex χ P).homology 1,
      (∀ k, HomologicalComplex.homologyMap (fibreMap χ (ψt k)) 1 c = 0) → c = 0 :=
    eq_zero_of_forall_map_eq_zero_of_iso (ιM 1) (fun k => ιN k 1)
      (fun k => (DerivedCategory.homologyFunctor _ 1).map (D.functor.map (ψ k)))
      (fun k => HomologicalComplex.homologyMap (fibreMap χ (ψt k)) 1) (fun k => hιψ k 1) h1
  have hdimc : ∀ k, Module.finrank K ((fibreComplex χ (Pk k)).homology 0) ≤ 1 := fun k =>
    (ιN k 0).toLinearEquiv.finrank_eq ▸ hdim k
  have hzc : ∀ k, ∃ z : unitComplex R ⟶ Pk k, DerivedCategory.Q.map (fibreMap χ z) ≠ 0 :=
    fun k => exists_fibreMap_ne_zero_of_functor_map_ne_zero χ D (eN k) (hτ _ (bQ k)) (hz k)
  have hnec : Nontrivial ((fibreComplex χ P).homology 0) :=
    (ιM 0).toLinearEquiv.injective.nontrivial
  obtain ⟨y, hy⟩ := exists_unit_map_homologyMap_ne_zero χ P aP bP hPfin hPproj Pk aQ bQ hQfin
    hQproj ψt h1c hdimc hzc hnec
  refine ⟨DerivedCategory.Q.map y ≫ eM.inv,
    fun h0 => functor_map_Q_map_ne_zero χ D y (hτ _ 0) 0 hy ?_⟩
  rw [Functor.map_comp] at h0
  rwa [← cancel_mono (D.functor.map eM.inv), zero_comp]

end Main

end StacksDraft.Perfect.FibreCycleLift

end
