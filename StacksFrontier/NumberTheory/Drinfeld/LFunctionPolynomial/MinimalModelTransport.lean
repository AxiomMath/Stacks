module

public import StacksFrontier.NumberTheory.Drinfeld.LFunctionPolynomial.MinimalCharSeries
public import StacksFrontier.Homology.Perfect.MinimalComplexFreeCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Minimal models in any module universe, and the characteristic series of an invertible
endomorphism

Let `A` be a local ring with residue field `κ` and `P` a bounded complex of finite projective
`A`-modules, its terms in any universe `max u w` above that of `A`. [Stacks, Tag 0BCC]
(`StacksDraft.Perfect.FibreCycleLift.exists_minimal_model`) is stated for modules in the universe
of `A`. Writing `P` in bases gives a complex with terms `A^{rᵢ}` in that universe. Its minimal
model, lifted back along `ModuleCat.uliftFunctor`, is a minimal complex `F` homotopy equivalent to
`P`.

For an endomorphism `φ` of `P` with a homotopy inverse, `det(1 - φ T | P)` is the same on `F`
(cyclicity and homotopy invariance of `FilteredDerived.alternatingCharSeries`). On `F` the
determinants of the degreewise maps are units (`Stacks.Drinfeld.isUnit_det_of_homotopy`). So
`det(1 - φ T | P)⁻¹ = P' / Q'` with unit top coefficients, `deg P' ≤ ∑_{i odd} rᵢ`,
`deg Q' ≤ ∑_{i even} rᵢ`, where `rᵢ = dim_κ Hⁱ(P ⊗_A κ)`. The ranks are read on `P ⊗_A κ`, which
computes the derived fibre `P ⊗ᴸ_A κ`.

## Main results

* `Stacks.Drinfeld.basisModel`, `Stacks.Drinfeld.basisModelIso`: a complex of finite free modules
  written in bases, and its universe lift recovers it.
* `Stacks.Drinfeld.exists_minimal_homotopyEquiv`: a minimal complex homotopy equivalent to `P`.
* `Stacks.Drinfeld.exists_polynomial_mul_inv_alternatingCharSeries_of_homotopy`: the quotient
  `P' / Q'` for an endomorphism of `P` with a homotopy inverse, with the fibre ranks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial PowerSeries Finset
open scoped TensorProduct

universe u w

namespace Stacks.Drinfeld

variable {A : Type u} [CommRing A]

section Model

/-- **A complex of free modules written in bases**: the complex with terms `A^{rᵢ}`, in the
universe of `A`, whose differentials are those of `P` read through the linear equivalences
`eᵢ : Pⁱ ≃ A^{rᵢ}`. -/
def basisModel (P : CochainComplex (ModuleCat.{w} A) ℤ) (r : ℤ → ℕ)
    (e : ∀ i, P.X i ≃ₗ[A] (Fin (r i) → A)) : CochainComplex (ModuleCat.{u} A) ℤ where
  X i := ModuleCat.of A (Fin (r i) → A)
  d i j := ModuleCat.ofHom ((e j).toLinearMap ∘ₗ (P.d i j).hom ∘ₗ (e i).symm.toLinearMap)
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [P.shape i j h]
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun t => t.hom ((e i).symm x)) (P.d_comp_d i j k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    simp [h]

/-- The universe lift of `basisModel P r e` is isomorphic to `P`. -/
def basisModelIso (P : CochainComplex (ModuleCat.{max u w} A) ℤ) (r : ℤ → ℕ)
    (e : ∀ i, P.X i ≃ₗ[A] (Fin (r i) → A)) :
    ((ModuleCat.uliftFunctor.{w, u} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (basisModel P r e) ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (ULift.moduleEquiv.trans (e i).symm).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (P.d i j).hom ((e i).symm x.down) =
        (e j).symm ((e j) ((P.d i j).hom ((e i).symm x.down)))
      rw [LinearEquiv.symm_apply_apply])

/-- A term of `basisModel P r e` vanishes where the corresponding term of `P` does. -/
theorem isZero_basisModel_X (P : CochainComplex (ModuleCat.{w} A) ℤ) (r : ℤ → ℕ)
    (e : ∀ i, P.X i ≃ₗ[A] (Fin (r i) → A)) {i : ℤ} (hi : IsZero (P.X i)) :
    IsZero ((basisModel P r e).X i) := by
  have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hi
  have : Subsingleton ((basisModel P r e).X i) := (e i).symm.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end Model

variable [IsLocalRing A]

omit [IsLocalRing A] in
/-- **The reduction of a map with image in `I N` vanishes.** -/
theorem extendScalars_map_eq_zero_of_range_le {M' N' : ModuleCat.{w} A} (f : M' ⟶ N')
    (I : Ideal A) (h : LinearMap.range f.hom ≤ I • (⊤ : Submodule A N')) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f = 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (TensorProduct.tmul A (1 : A ⧸ I) (f.hom x) : TensorProduct A (A ⧸ I) N') = 0
  apply (TensorProduct.quotTensorEquivQuotSMul (N' : Type w) I).injective
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero]
  exact h (LinearMap.mem_range_self f.hom x)

/-- A module isomorphic to `R^n` (in a universe lift) has rank `n`. -/
private theorem finrank_eq_of_nonempty_iso {R : Type u} [CommRing R] [Nontrivial R]
    {M : ModuleCat.{max u w} R} {n : ℕ}
    (h : Nonempty (M ≅ ModuleCat.of R (ULift.{w} (Fin n → R)))) :
    Module.finrank R M = n := by
  rw [h.some.toLinearEquiv.finrank_eq, ULift.moduleEquiv.finrank_eq, Module.finrank_fin_fun]

/-- The reduction to the residue field of a module isomorphic to `A^n` is isomorphic to `κ^n`. -/
private theorem nonempty_extendScalars_iso {F : ModuleCat.{max u w} A} {n : ℕ}
    (h : Nonempty (F ≅ ModuleCat.of A (ULift.{w} (Fin n → A)))) :
    Nonempty ((ModuleCat.extendScalars (IsLocalRing.residue A)).obj F ≅
      ModuleCat.of (IsLocalRing.ResidueField A) (ULift.{w} (Fin n → IsLocalRing.ResidueField A))) :=
  ⟨(ModuleCat.extendScalars (IsLocalRing.residue A)).mapIso h.some ≪≫
    (StacksDraft.Perfect.extendScalars_standard_free_iso.{u, w} _ n).some⟩

/-- **A complex whose fibre cohomology has the ranks of its terms is minimal.** If `Fⁱ ≅ A^{rᵢ}`
and `dim_κ Hⁱ(F ⊗_A κ) = rᵢ` for every `i`, every differential of `F` has image in `𝔪 F`. -/
theorem range_d_le_maximalIdeal_smul_of_finrank_fibre_homology
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℤ → ℕ)
    (hX : ∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A))))
    (hr : ∀ i, Module.finrank (IsLocalRing.ResidueField A)
      ((StacksDraft.Perfect.FibreCycleLift.fibreComplex (IsLocalRing.residue A) F).homology i) =
        r i) (i j : ℤ) :
    LinearMap.range (F.d i j).hom ≤ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j)) := by
  let κ := IsLocalRing.residue A
  have hκX : ∀ i, Nonempty ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).X i ≅
      ModuleCat.of (IsLocalRing.ResidueField A) (ULift.{u} (Fin (r i) → _))) := fun i =>
    nonempty_extendScalars_iso (hX i)
  have hfinX : ∀ i, Module.Finite (IsLocalRing.ResidueField A)
      ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).X i) := fun i =>
    Module.Finite.equiv (hκX i).some.toLinearEquiv.symm
  have hlenX : ∀ i, Module.length (IsLocalRing.ResidueField A)
      ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).X i) ≠ ⊤ := fun i => by
    have := hfinX i
    rw [Module.length_eq_finrank]
    exact ENat.natCast_ne_top _
  have hfinH : ∀ i, Module.Finite (IsLocalRing.ResidueField A)
      ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).homology i) := fun i => by
    have hle :=
      (StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).moduleCat_length_homology_le i
    have : IsFiniteLength (IsLocalRing.ResidueField A)
        ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).homology i) := by
      exact Module.length_ne_top_iff.1 (ne_top_of_le_ne_top (hlenX i) hle)
    have : IsNoetherian (IsLocalRing.ResidueField A)
        ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).homology i) :=
      ((isFiniteLength_iff_isNoetherian_isArtinian).1 this).1
    infer_instance
  have hdκ : ∀ i j, (StacksDraft.Perfect.FibreCycleLift.fibreComplex κ F).d i j = 0 :=
    HomologicalComplex.moduleCat_d_eq_zero_of_forall_length_homology_eq _
      (fun i => by
        rw [Module.length_eq_finrank, Module.length_eq_finrank, hr i,
          finrank_eq_of_nonempty_iso (hκX i)])
      hlenX
  exact LinearMap.range_le_smul_top_of_extendScalars_map_eq_zero (F.d i j) _ (hdκ i j)

/-- **A complex with the fibre ranks of its terms vanishes where a homotopy equivalent one does.**
If `Fⁱ ≅ A^{rᵢ}` with `rᵢ = dim_κ Hⁱ(F ⊗_A κ)` and `F` is homotopy equivalent to `P`, then `Fⁱ = 0`
wherever `Pⁱ = 0`. -/
theorem isZero_X_of_finrank_fibre_homology {F P : CochainComplex (ModuleCat.{u} A) ℤ}
    (r : ℤ → ℕ) (hX : ∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A))))
    (hr : ∀ i, Module.finrank (IsLocalRing.ResidueField A)
      ((StacksDraft.Perfect.FibreCycleLift.fibreComplex (IsLocalRing.residue A) F).homology i) =
        r i) (h : HomotopyEquiv F P) {i : ℤ} (hi : IsZero (P.X i)) : IsZero (F.X i) := by
  let κ := IsLocalRing.residue A
  have hr0 : r i = 0 := by
    rw [← hr i]
    have hz : IsZero ((StacksDraft.Perfect.FibreCycleLift.fibreComplex κ P).homology i) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ ((ModuleCat.extendScalars κ).map_isZero hi)
    rw [(((ModuleCat.extendScalars κ).mapHomotopyEquiv h).toHomologyIso
      i).toLinearEquiv.finrank_eq]
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  have : Subsingleton (ULift.{u} (Fin (r i) → A)) := by
    rw [hr0]
    infer_instance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (hX i).some

/-- **A minimal complex homotopy equivalent to `P`.** Over a local ring, a bounded complex `P` of
finite projective modules in a universe above that of the ring is homotopy equivalent to a bounded
complex `F` of finite projective modules all of whose differentials have image in `𝔪 F`. -/
theorem exists_minimal_homotopyEquiv (P : CochainComplex (ModuleCat.{max u w} A) ℤ)
    (hP : FilteredDerived.finiteProjectiveComplex A P) :
    ∃ (F : CochainComplex (ModuleCat.{max u w} A) ℤ) (r : ℤ → ℕ),
      (∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{w} (Fin (r i) → A)))) ∧
      FilteredDerived.finiteProjectiveComplex A F ∧
      (∀ i j, LinearMap.range (F.d i j).hom ≤
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j))) ∧
      Nonempty (HomotopyEquiv F P) := by
  classical
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hfp⟩ := hP
  have : P.IsStrictlyGE a := ha
  have : P.IsStrictlyLE b := hb
  have hfree : ∀ i, Module.Free A (P.X i) := fun i => by
    have := (hfp i).1
    have := (hfp i).2
    exact Module.free_of_flat_of_isLocalRing
  let r : ℤ → ℕ := fun i => Module.finrank A (P.X i)
  let e : ∀ i, P.X i ≃ₗ[A] (Fin (r i) → A) := fun i => by
    have := hfree i
    have := (hfp i).2
    exact (Module.finBasis A (P.X i)).equivFun
  let P₀ := basisModel P r e
  have : P₀.IsStrictlyGE a := (P₀.isStrictlyGE_iff a).2 fun i hi =>
    isZero_basisModel_X P r e (P.isZero_of_isStrictlyGE a i hi)
  have : P₀.IsStrictlyLE b := (P₀.isStrictlyLE_iff b).2 fun i hi =>
    isZero_basisModel_X P r e (P.isZero_of_isStrictlyLE b i hi)
  obtain ⟨F₀, r', hX, hr, ⟨h⟩⟩ := StacksDraft.Perfect.FibreCycleLift.exists_minimal_model P₀ a b
    (fun i => inferInstanceAs (Module.Finite A (Fin (r i) → A)))
    (fun i => inferInstanceAs (Module.Projective A (Fin (r i) → A)))
  have hmin₀ := range_d_le_maximalIdeal_smul_of_finrank_fibre_homology F₀ r' hX hr
  -- lift back to the universe of `P`
  let U := ModuleCat.uliftFunctor.{w, u} A
  let L := U.mapHomologicalComplex (ComplexShape.up ℤ)
  let eX : ∀ i, (L.obj F₀).X i ≃ₗ[A] ULift.{w} (Fin (r' i) → A) := fun i =>
    ULift.moduleEquiv.trans ((hX i).some.toLinearEquiv.trans
      (ULift.moduleEquiv.trans ULift.moduleEquiv.symm))
  have hLz : ∀ i, IsZero (P₀.X i) → IsZero ((L.obj F₀).X i) := fun i hi =>
    U.map_isZero (isZero_X_of_finrank_fibre_homology r' hX hr h hi)
  refine ⟨L.obj F₀, r', fun i => ⟨(eX i).toModuleIso⟩, ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i => ⟨?_, ?_⟩⟩,
    fun i j => ?_, ⟨(U.mapHomotopyEquiv h).trans (HomotopyEquiv.ofIso (basisModelIso P r e))⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff (K := L.obj F₀) a).2 fun i hi =>
      hLz i (P₀.isZero_of_isStrictlyGE a i hi)
  · exact (CochainComplex.isStrictlyLE_iff (K := L.obj F₀) b).2 fun i hi =>
      hLz i (P₀.isZero_of_isStrictlyLE b i hi)
  · exact Module.Projective.of_equiv (eX i).symm
  · exact Module.Finite.equiv (eX i).symm
  · rintro _ ⟨x, rfl⟩
    exact map_mem_smul_top (ULift.moduleEquiv.symm : F₀.X j ≃ₗ[A] ULift.{w} (F₀.X j)).toLinearMap
      (hmin₀ i j (LinearMap.mem_range_self _ x.down))

/-- **The fibre ranks** `dim_κ Hⁱ(P ⊗_A κ)` of a complex of `A`-modules: the dimensions of the
cohomology of its termwise reduction to the residue field. For a bounded above complex of
projective modules `P ⊗_A κ` computes the derived fibre `P ⊗ᴸ_A κ`. -/
def fibreRank (P : CochainComplex (ModuleCat.{max u w} A) ℤ) (i : ℤ) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField A)
    ((((ModuleCat.extendScalars (IsLocalRing.residue A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i)

/-- On a minimal complex with terms `A^{rᵢ}` the fibre ranks are the `rᵢ`: the reduction has zero
differentials. -/
theorem fibreRank_eq_of_minimal (F : CochainComplex (ModuleCat.{max u w} A) ℤ) (r : ℤ → ℕ)
    (hX : ∀ i, Nonempty (F.X i ≅ ModuleCat.of A (ULift.{w} (Fin (r i) → A))))
    (hmin : ∀ i j, LinearMap.range (F.d i j).hom ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j))) (i : ℤ) :
    fibreRank F i = r i := by
  let K := ((ModuleCat.extendScalars (IsLocalRing.residue A)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj F
  have hd : ∀ i j, K.d i j = 0 := fun i j =>
    extendScalars_map_eq_zero_of_range_le (F.d i j) _ (hmin i j)
  let e1 : K.homology i ≅ K.X i :=
    (K.isoHomologyπ (i - 1) i (by simp) (hd _ _)).symm ≪≫ K.iCyclesIso i (i + 1) (by simp) (hd _ _)
  exact finrank_eq_of_nonempty_iso ⟨e1 ≪≫ (nonempty_extendScalars_iso (hX i)).some⟩

/-- Homotopy equivalent complexes have the same fibre ranks. -/
theorem fibreRank_eq_of_homotopyEquiv {F P : CochainComplex (ModuleCat.{max u w} A) ℤ}
    (h : HomotopyEquiv F P) (i : ℤ) : fibreRank F i = fibreRank P i :=
  (((ModuleCat.extendScalars (IsLocalRing.residue A)).mapHomotopyEquiv h).toHomologyIso
    i).toLinearEquiv.finrank_eq

/-- **The characteristic series of an endomorphism with a homotopy inverse.** Let `P` be a
bounded complex of finite projective modules over a local ring and `φ` an endomorphism of `P`
with a homotopy inverse `ψ`. Then `Q' · det(1 - φ T | P)⁻¹ = P'` for polynomials `P'`, `Q'` of
degrees at most `∑_{i odd} rᵢ` and `∑_{i even} rᵢ`, `rᵢ = dim_κ Hⁱ(P ⊗_A κ)`, whose coefficients in
those degrees are units. -/
theorem exists_polynomial_mul_inv_alternatingCharSeries_of_homotopy
    (P : CochainComplex (ModuleCat.{max u w} A) ℤ)
    (hP : FilteredDerived.finiteProjectiveComplex A P) {φ ψ : P ⟶ P}
    (H : Homotopy (φ ≫ ψ) (𝟙 P)) :
    ∃ S : Finset ℤ, ∃ P' Q' : A[X], P'.natDegree ≤ ∑ i ∈ S with ¬ Even i, fibreRank P i ∧
      Q'.natDegree ≤ ∑ i ∈ S with Even i, fibreRank P i ∧
      IsUnit (P'.coeff (∑ i ∈ S with ¬ Even i, fibreRank P i)) ∧
      IsUnit (Q'.coeff (∑ i ∈ S with Even i, fibreRank P i)) ∧
      (Q' : A⟦X⟧) * (((FilteredDerived.alternatingCharSeries A P hP φ)⁻¹ : (A⟦X⟧)ˣ) : A⟦X⟧) =
        P' := by
  classical
  obtain ⟨F, r, hX, hF, hmin, ⟨h⟩⟩ := exists_minimal_homotopyEquiv P hP
  let φF := h.hom ≫ φ ≫ h.inv
  let ψF := h.hom ≫ ψ ≫ h.inv
  have HF : Homotopy (φF ≫ ψF) (𝟙 F) := by
    have h1 : Homotopy (φF ≫ ψF) (h.hom ≫ (φ ≫ (h.inv ≫ h.hom) ≫ (ψ ≫ h.inv))) :=
      Homotopy.ofEq (by simp [φF, ψF, Category.assoc])
    have h2 : Homotopy (h.hom ≫ (φ ≫ (h.inv ≫ h.hom) ≫ (ψ ≫ h.inv)))
        (h.hom ≫ (φ ≫ 𝟙 P ≫ (ψ ≫ h.inv))) :=
      ((h.homotopyInvHomId.compRight (ψ ≫ h.inv)).compLeft φ).compLeft h.hom
    have h3 : Homotopy (h.hom ≫ (φ ≫ 𝟙 P ≫ (ψ ≫ h.inv))) (h.hom ≫ ((φ ≫ ψ) ≫ h.inv)) :=
      Homotopy.ofEq (by simp [Category.assoc])
    have h4 : Homotopy (h.hom ≫ ((φ ≫ ψ) ≫ h.inv)) (h.hom ≫ (𝟙 P ≫ h.inv)) :=
      (H.compRight h.inv).compLeft h.hom
    have h5 : Homotopy (h.hom ≫ (𝟙 P ≫ h.inv)) (h.hom ≫ h.inv) := Homotopy.ofEq (by simp)
    exact (((h1.trans h2).trans h3).trans h4).trans (h5.trans h.homotopyHomInvId)
  have halt : FilteredDerived.alternatingCharSeries A F hF φF =
      FilteredDerived.alternatingCharSeries A P hP φ := by
    rw [show φF = h.hom ≫ (φ ≫ h.inv) from rfl,
      FilteredDerived.alternatingCharSeries_comp_comm A F P hF hP h.hom (φ ≫ h.inv)]
    exact FilteredDerived.alternatingCharSeries_eq_of_homotopy A P hP
      ((Homotopy.ofEq (Category.assoc _ _ _)).trans
        ((h.homotopyInvHomId.compLeft φ).trans (Homotopy.ofEq (Category.comp_id _))))
  let S := (FilteredDerived.finite_nonzero_degrees A F hF).toFinset
  have hS : ∀ i ∉ S, IsZero (F.X i) := fun i hi => by
    by_contra h'
    exact hi ((FilteredDerived.finite_nonzero_degrees A F hF).mem_toFinset.2 h')
  have hrank : ∀ i, Module.finrank A (F.X i) = fibreRank P i := fun i => by
    rw [← fibreRank_eq_of_homotopyEquiv h, fibreRank_eq_of_minimal F r hX hmin,
      finrank_eq_of_nonempty_iso (hX i)]
  obtain ⟨P', Q', h1, h2, h3, h4, h5⟩ :=
    exists_polynomial_mul_inv_alternatingCharSeries F hF hmin HF S hS
  simp only [hrank] at h1 h2 h3 h4
  rw [halt] at h5
  exact ⟨S, P', Q', h1, h2, h3, h4, h5⟩

universe t

/-- **The characteristic series of an automorphism of a perfect object over a local ring.** For
a perfect object `K` of `D(A)`, `A` local, and an automorphism `φ` of `K`,
`Q' · det(1 - φ T | K)⁻¹ = P'` for polynomials `P'`, `Q'` of degrees at most `∑_{i odd} rᵢ` and
`∑_{i even} rᵢ`, whose coefficients in those degrees are units. Here `rᵢ = dim_κ Hⁱ(P ⊗_A κ)` for
the chosen finite projective representative `P` of `K` (`FilteredDerived.perfectRep`), so
`rᵢ = dim_κ Hⁱ(K ⊗ᴸ_A κ)`. The representatives of `φ` and of `φ⁻¹` on `P` are homotopy inverse. -/
theorem exists_polynomial_mul_inv_perfectDerivedCharSeries
    [HasDerivedCategory.{t} (ModuleCat.{max u w} A)]
    (K : DerivedCategory (ModuleCat.{max u w} A)) (hK : StacksDraft.Perfect.IsPerfect K)
    (φ : K ⟶ K) [IsIso φ] :
    ∃ S : Finset ℤ, ∃ P' Q' : A[X],
      P'.natDegree ≤ ∑ i ∈ S with ¬ Even i, fibreRank (FilteredDerived.perfectRep A K hK) i ∧
      Q'.natDegree ≤ ∑ i ∈ S with Even i, fibreRank (FilteredDerived.perfectRep A K hK) i ∧
      IsUnit (P'.coeff (∑ i ∈ S with ¬ Even i, fibreRank (FilteredDerived.perfectRep A K hK) i)) ∧
      IsUnit (Q'.coeff (∑ i ∈ S with Even i, fibreRank (FilteredDerived.perfectRep A K hK) i)) ∧
      (Q' : A⟦X⟧) *
          (((FilteredDerived.perfectDerivedCharSeries A K hK φ)⁻¹ : (A⟦X⟧)ˣ) : A⟦X⟧) = P' := by
  classical
  let P := FilteredDerived.perfectRep A K hK
  let hP := FilteredDerived.perfectRep_spec A K hK
  let e := FilteredDerived.perfectRepIso A K hK
  let : CochainComplex.IsKProjective P := by
    obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
    have : P.IsStrictlyLE d := hd
    have (i : ℤ) : Module.Projective A (P.X i) := (hproj i).1
    have (i : ℤ) : Projective (P.X i) := inferInstance
    exact CochainComplex.isKProjective_of_projective P d
  let Qt := HomotopyCategory.quotient (ModuleCat.{max u w} A) (ComplexShape.up ℤ)
  let qP := Qt.obj P
  let α : DerivedCategory.Qh.obj qP ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max u w} A)).app P ≪≫ e
  have hbij := CochainComplex.IsKProjective.Qh_map_bijective P qP
  let gH : (K ⟶ K) → (qP ⟶ qP) := fun θ => (hbij.surjective (α.hom ≫ θ ≫ α.inv)).choose
  have hgH : ∀ θ, DerivedCategory.Qh.map (gH θ) = α.hom ≫ θ ≫ α.inv := fun θ =>
    (hbij.surjective _).choose_spec
  let g : (K ⟶ K) → (P ⟶ P) := fun θ => Qt.preimage (gH θ)
  have hg : ∀ θ, Qt.map (g θ) = gH θ := fun θ => Qt.map_preimage _
  have hdef : FilteredDerived.perfectDerivedCharSeries A K hK φ =
      FilteredDerived.alternatingCharSeries A P hP (g φ) := rfl
  have H : Homotopy (g φ ≫ g (inv φ)) (𝟙 P) := by
    apply HomotopyCategory.homotopyOfEq
    rw [CategoryTheory.Functor.map_comp, hg, hg, CategoryTheory.Functor.map_id]
    apply hbij.injective
    rw [CategoryTheory.Functor.map_comp, hgH, hgH, CategoryTheory.Functor.map_id]
    simp
  rw [hdef]
  exact exists_polynomial_mul_inv_alternatingCharSeries_of_homotopy P hP H

end Stacks.Drinfeld

end
