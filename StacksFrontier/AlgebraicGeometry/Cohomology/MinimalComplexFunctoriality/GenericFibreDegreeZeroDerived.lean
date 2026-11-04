module

public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.GenericFibreDegreeZero

/-!
# Semicontinuity and a degree-zero lift over a local domain, in the derived category

Let `A` be a local ring, `χ : A ⟶ L` a local homomorphism to a field (for instance the residue
map), and let `M` be a pseudo-coherent object of `D(A)`. Represent `M` by the minimal complex of
Stacks 0BCC, whose term in degree `i` is free of rank `dim_L Hⁱ(M ⊗ᴸ L)`. Then:

* for every homomorphism `A ⟶ K` to a field, `dim_K Hⁱ(M ⊗ᴸ K) ≤ dim_L Hⁱ(M ⊗ᴸ L)`;
* if `A` is a domain, `ι : A ⟶ K` is injective (for instance into the fraction field),
  `H⁰(M ⊗ᴸ L)` is one-dimensional and `H⁰(M ⊗ᴸ K) ≠ 0`, then there is a map `A[0] ⟶ M` whose
  image `L[0] ⟶ M ⊗ᴸ L` is nonzero;
* if `A` is a valuation ring, `ι : A ⟶ K` is injective with every element of `K` a fraction of
  elements of `A`, and some map `K[0] ⟶ M ⊗ᴸ K` is nonzero, then there is a map `A[0] ⟶ M` whose
  image `L[0] ⟶ M ⊗ᴸ L` is nonzero.

The derived tensor products are arbitrary total derived extension-of-scalars data.

## Main results

* `StacksDraft.Perfect.FibreCycleLift.finrank_homology_derived_le`:
  `dim_K Hⁱ(M ⊗ᴸ K) ≤ dim_L Hⁱ(M ⊗ᴸ L)`, semicontinuity of the dimension of the cohomology of
  the derived fibres.
* `StacksDraft.Perfect.FibreCycleLift.exists_unit_map_ne_zero_of_nontrivial_generic`: over a
  local domain, a map `A[0] ⟶ M` with nonzero image along `χ`, when `H⁰(M ⊗ᴸ L)` is
  one-dimensional and `H⁰(M ⊗ᴸ K) ≠ 0`.
* `StacksDraft.Perfect.FibreCycleLift.exists_cycle_notMem_of_valuationRing`: over a valuation
  ring, a complex whose generic fibre has a nonzero degree-zero cycle has a degree-zero cycle not
  in `𝔪 F⁰`.
* `StacksDraft.Perfect.FibreCycleLift.exists_unit_map_ne_zero_of_valuationRing`: over a valuation
  ring, a map `A[0] ⟶ M` with nonzero image along `χ`, when some map `K[0] ⟶ M ⊗ᴸ K` is nonzero.

## References

* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

namespace StacksDraft.Perfect.FibreCycleLift

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

section LocalRing

variable [IsLocalRing A]

/-- The minimal complex of Stacks 0BCC: a pseudo-coherent `M ∈ D(A)` is represented by a
bounded above complex `P` of finite free modules of ranks `r i`, where `r i` is the dimension of
the cohomology of the residual fibre of `P`. -/
private theorem exists_model (M : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) (_ : P.IsStrictlyLE b)
      (_ : ∀ i, Projective (P.X i)) (r : ℤ → ℕ),
      (∀ i, Nonempty (P.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A)))) ∧
      (∀ i, Module.finrank (IsLocalRing.ResidueField A)
        ((fibreComplex (IsLocalRing.residue A) P).homology i) = r i) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let D₀ := totalDerivedExtensionScalars.{u, u, u} (IsLocalRing.residue A)
  obtain ⟨-, b, -, P, hPb, ⟨hX, ⟨eK⟩⟩, -⟩ :=
    StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing_of_datum.{u, u}
      D₀ M hM
  have hproj : ∀ i, Projective (P.X i) := fun i =>
    Projective.of_iso (hX i).some.symm (ModuleCat.projective_of_free
      ((Pi.basisFun A _).map ULift.moduleEquiv.symm))
  refine ⟨P, b, hPb, hproj, _, hX, fun i => ?_, ⟨eK⟩⟩
  have := D₀.comparison_isIso_of_projective P b
  exact ((((DerivedCategory.homologyFunctor _ i).mapIso
      (D₀.functor.mapIso eK.symm ≪≫ asIso (D₀.comparison.app P)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _)).toLinearEquiv.finrank_eq).symm

/-- The identification of the cohomology of a derived fibre of `Q P`, for a bounded above
complex `P` of projectives, with the cohomology of the termwise fibre of `P`. -/
private def homologyIso {L : Type u} [Field L] {ρ : A →+* L}
    (D : TotalDerivedExtensionScalars.{u, u, u} ρ) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] {M : DerivedCategory (ModuleCat.{u} A)}
    (e : DerivedCategory.Q.obj P ≅ M) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj (D.functor.obj M) ≅
      (fibreComplex ρ P).homology i :=
  have := D.comparison_isIso_of_projective P b
  (DerivedCategory.homologyFunctor _ i).mapIso
      (D.functor.mapIso e.symm ≪≫ asIso (D.comparison.app P)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _

/-- Along a local homomorphism to a field, the cohomology of the fibre of a minimal complex has
dimension the rank of the term: the differentials of that fibre vanish. -/
private theorem finrank_homology_fibreComplex_eq {L : Type u} [Field L] (χ : A →+* L)
    [IsLocalHom χ] (P : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℤ → ℕ)
    (hX : ∀ i, Nonempty (P.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A))))
    (hH : ∀ i, Module.finrank (IsLocalRing.ResidueField A)
      ((fibreComplex (IsLocalRing.residue A) P).homology i) = r i) (i : ℤ) :
    Module.finrank L ((fibreComplex χ P).homology i) = r i := by
  rw [← (zeroDiffHomologyIso (fibreComplex χ P) (fibreComplex_d_eq_zero χ P r hX hH)
    i).toLinearEquiv.finrank_eq]
  exact (finrank_fibre_ulift χ (r i) (P.X i) (hX i).some).1

/-- The terms of the unit complex are projective. -/
private theorem projective_unitComplex_X {R : Type u} [CommRing R] (i : ℤ) :
    Projective ((unitComplex R).X i) := by
  by_cases hi : i = 0
  · subst hi
    exact Projective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).symm inferInstance
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).projective

/-- The unit complex is concentrated in degrees `≤ 0`. -/
private theorem isStrictlyLE_unitComplex (R : Type u) [CommRing R] :
    (unitComplex R).IsStrictlyLE 0 := by
  show ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    (ModuleCat.of R R)).IsStrictlyLE 0
  infer_instance

/-- A local homomorphism to a field sends an element of a finite free module outside `𝔪 M` to a
nonzero element of the fibre. -/
private theorem fibreElt_ne_zero_of_notMem {L : Type u} [Field L] (χ : A →+* L)
    [IsLocalHom χ] {M : ModuleCat.{u} A} {n : ℕ}
    (e₀ : M ≅ ModuleCat.of A (ULift.{u} (Fin n → A))) {z : M}
    (hz : z ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) : fibreElt χ M z ≠ 0 := by
  have : Module.Free A M := Module.Free.of_equiv e₀.toLinearEquiv.symm
  exact fun h => hz (mem_of_fibreElt_eq_zero χ _ _ h)

/-- A degree-zero cycle `z` of a minimal complex `P` representing `M` whose image in `L ⊗ P⁰`
is nonzero gives a map `A[0] ⟶ M` with nonzero image under derived extension of scalars along
the local homomorphism `χ : A ⟶ L`. -/
private theorem exists_unit_map_ne_zero_of_cycle {L : Type u} [Field L]
    {χ : A →+* L} [IsLocalHom χ] (Dχ : TotalDerivedExtensionScalars.{u, u, u} χ)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [P.IsStrictlyLE b] [∀ i, Projective (P.X i)]
    (r : ℤ → ℕ) (hX : ∀ i, Nonempty (P.X i ≅ ModuleCat.of A (ULift.{u} (Fin (r i) → A))))
    (hH : ∀ i, Module.finrank (IsLocalRing.ResidueField A)
      ((fibreComplex (IsLocalRing.residue A) P).homology i) = r i)
    {M : DerivedCategory (ModuleCat.{u} A)} (e : DerivedCategory.Q.obj P ≅ M)
    (z : P.X 0) (hz0 : P.d 0 1 z = 0) (hzχ : fibreElt χ (P.X 0) z ≠ 0) :
    ∃ y : DerivedCategory.Q.obj (unitComplex A) ⟶ M, Dχ.functor.map y ≠ 0 := by
  let φ : ModuleCat.of A A ⟶ P.X 0 := ModuleCat.ofHom (LinearMap.toSpanSingleton A _ z)
  let zt : unitComplex A ⟶ P := HomologicalComplex.mkHomFromSingle φ (by
    intro k hk
    have hk' : k = 1 := by simpa [ComplexShape.up_Rel] using hk.symm
    subst hk'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show P.d 0 1 (x • z) = 0
    rw [map_smul, hz0, smul_zero])
  have hzt : zt.f 0 (unitGen A) = z := by
    show ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).hom ≫ φ)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)).inv
        (1 : A)) = z
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id_assoc]
    show (1 : A) • z = z
    rw [one_smul]
  have : (unitComplex A).IsStrictlyLE 0 := isStrictlyLE_unitComplex A
  have := projective_unitComplex_X (R := A)
  have hτU := Dχ.comparison_isIso_of_projective (unitComplex A) 0
  refine ⟨DerivedCategory.Q.map zt ≫ e.hom, fun h0' => hzχ ?_⟩
  rw [Functor.map_comp] at h0'
  have h1 : Dχ.functor.map (DerivedCategory.Q.map zt) = 0 := by
    rwa [← cancel_mono (Dχ.functor.map e.hom), zero_comp]
  have hn : Dχ.functor.map (DerivedCategory.Q.map zt) ≫ Dχ.comparison.app P =
      Dχ.comparison.app (unitComplex A) ≫ DerivedCategory.Q.map (fibreMap χ zt) :=
    Dχ.comparison.naturality zt
  rw [h1, zero_comp] at hn
  have hQ0 : DerivedCategory.Q.map (fibreMap χ zt) = 0 := by
    let τU : Dχ.functor.obj (DerivedCategory.Q.obj (unitComplex A)) ≅
        DerivedCategory.Q.obj (fibreComplex χ (unitComplex A)) :=
      @asIso _ _ _ _ (Dχ.comparison.app (unitComplex A)) hτU
    rw [← cancel_epi τU.hom, comp_zero]
    exact hn.symm
  have h2 := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} L) 0).hom.naturality
    (fibreMap χ zt)
  have h3 : (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} L) 0).map
      (fibreMap χ zt) = 0 := by
    simp only [Functor.comp_map, hQ0, Functor.map_zero]
  rw [h3, zero_comp] at h2
  have h4 : HomologicalComplex.homologyMap (fibreMap χ zt) 0 = 0 :=
    (cancel_epi ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} L) 0).hom.app
        (fibreComplex χ (unitComplex A)))).1 (h2.symm.trans comp_zero.symm)
  have hUd : ∀ i j, (fibreComplex χ (unitComplex A)).d i j = 0 := by
    intro i j
    show (ModuleCat.extendScalars χ).map ((unitComplex A).d i j) = 0
    rw [HomologicalComplex.single_obj_d, Functor.map_zero]
  have hPd := fibreComplex_d_eq_zero χ P r hX hH
  have hnat := zeroDiffHomologyIso_hom_naturality hUd hPd (fibreMap χ zt) 0
  rw [h4, comp_zero] at hnat
  have h5 : (fibreMap χ zt).f 0 = 0 := by
    rw [← cancel_mono (zeroDiffHomologyIso (fibreComplex χ P) hPd 0).hom, zero_comp]
    exact hnat.symm
  have h6 := congrArg (fun ψ => ψ.hom (fibreElt χ _ (unitGen A))) h5
  change (ModuleCat.extendScalars χ).map (zt.f 0) (fibreElt χ _ (unitGen A)) = 0 at h6
  rwa [map_fibreElt, hzt] at h6


/-- **Semicontinuity of the cohomology of derived fibres over a local ring.** Let `M ∈ D(A)` be
pseudo-coherent, `A` local, and let `χ : A ⟶ L` be a local homomorphism to a field. For a
derived extension of scalars along any homomorphism `A ⟶ K` to a field,
`dim_K Hⁱ(M ⊗ᴸ K) ≤ dim_L Hⁱ(M ⊗ᴸ L)`. -/
theorem finrank_homology_derived_le {L : Type u} [Field L] {χ : A →+* L} [IsLocalHom χ]
    (Dχ : TotalDerivedExtensionScalars.{u, u, u} χ)
    {K : Type u} [Field K] {ρ : A →+* K} (D : TotalDerivedExtensionScalars.{u, u, u} ρ)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M)
    (i : ℤ) :
    Module.finrank K ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj
        (D.functor.obj M)) ≤
      Module.finrank L ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj
        (Dχ.functor.obj M)) := by
  obtain ⟨P, b, _, _, r, hX, hH, ⟨e⟩⟩ := exists_model M hM
  rw [(homologyIso D P b e i).toLinearEquiv.finrank_eq,
    (homologyIso Dχ P b e i).toLinearEquiv.finrank_eq,
    finrank_homology_fibreComplex_eq χ P r hX hH i]
  exact finrank_homology_fibreComplex_le ρ P r hX i

/-- **A degree-zero lift over a local domain.** Let `M ∈ D(A)` be pseudo-coherent, `A` a local
domain, let `χ : A ⟶ L` be a local homomorphism and `ι : A ⟶ K` an injective homomorphism to
fields. If `H⁰(M ⊗ᴸ L)` is one-dimensional and `H⁰(M ⊗ᴸ K) ≠ 0`, then some map `A[0] ⟶ M` has
nonzero image under derived extension of scalars along `χ`. -/
theorem exists_unit_map_ne_zero_of_nontrivial_generic [IsDomain A] {L : Type u} [Field L]
    {χ : A →+* L} [IsLocalHom χ] (Dχ : TotalDerivedExtensionScalars.{u, u, u} χ)
    {K : Type u} [Field K] {ι : A →+* K} (hι : Function.Injective ι)
    (Dι : TotalDerivedExtensionScalars.{u, u, u} ι)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M)
    (h0 : Module.finrank L
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) 0).obj (Dχ.functor.obj M)) = 1)
    (hgen : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) 0).obj
      (Dι.functor.obj M))) :
    ∃ y : DerivedCategory.Q.obj (unitComplex A) ⟶ M, Dχ.functor.map y ≠ 0 := by
  classical
  obtain ⟨P, b, _, _, r, hX, hH, ⟨e⟩⟩ := exists_model M hM
  have hr0 : r 0 = 1 := by
    rwa [← finrank_homology_fibreComplex_eq χ P r hX hH 0,
      ← (homologyIso Dχ P b e 0).toLinearEquiv.finrank_eq]
  obtain ⟨e₀⟩ := hX 0
  rw [hr0] at e₀
  have hfree1 : Module.Free A (P.X 1) := Module.Free.of_equiv (hX 1).some.toLinearEquiv.symm
  have hgen' : Nontrivial ((fibreComplex ι P).homology 0) :=
    (homologyIso Dι P b e 0).toLinearEquiv.injective.nontrivial
  obtain ⟨hd, z, hz0, hzne⟩ := exists_cycle_fibreElt_ne_zero_of_nontrivial_generic ι hι P e₀ hgen'
  have hzχ := fibreElt_ne_zero_of_notMem χ e₀
    fun hm => hzne (fibreElt_eq_zero_of_mem (IsLocalRing.residue A) _ _ hm)
  exact exists_unit_map_ne_zero_of_cycle Dχ P b r hX hH e z (by rw [hd]; rfl) hzχ

end LocalRing

section ValuationRing

/-- In a valuation ring, a nonempty finite family has a member dividing all the others. -/
private theorem exists_dvd_forall {ι : Type*} {R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R]
    (t : Finset ι) (ht : t.Nonempty) (f : ι → R) : ∃ j ∈ t, ∀ i ∈ t, f j ∣ f i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | insert a t ha ih =>
    rcases t.eq_empty_or_nonempty with rfl | hne
    · exact ⟨a, Finset.mem_insert_self _ _, by simp⟩
    · obtain ⟨j, hj, hjd⟩ := ih hne
      rcases ValuationRing.dvd_total (f a) (f j) with h | h
      · refine ⟨a, Finset.mem_insert_self _ _, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact dvd_rfl
        · exact h.trans (hjd i hi)
      · refine ⟨j, Finset.mem_insert_of_mem hj, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hjd i hi

/-- If every element of `K` is a fraction of elements of `A`, every element of `K ⊗_A M` has a
multiple by a nonzero scalar from `A` of the form `1 ⊗ x`. -/
private theorem exists_smul_eq_fibreElt_of_forall_fraction {K : Type u} [Field K] (ι : A →+* K)
    (hfrac : ∀ k : K, ∃ a c : A, ι c ≠ 0 ∧ k * ι c = ι a) (M : ModuleCat.{u} A)
    (w : (ModuleCat.extendScalars ι).obj M) :
    ∃ (c : A) (x : M), ι c ≠ 0 ∧ ι c • w = fibreElt ι M x := by
  have hw : w ∈ (Submodule.span K (Set.range (fibreElt ι M)) :
      Submodule K ((ModuleCat.extendScalars ι).obj M)) := by
    rw [fibreElt_span]
    exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    exact ⟨1, x, by simp, by rw [map_one, one_smul]⟩
  | zero => exact ⟨1, 0, by simp, by rw [smul_zero]; exact (TensorProduct.tmul_zero _ _).symm⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, x₁, hc₁, h₁⟩ := h₁
    obtain ⟨c₂, x₂, hc₂, h₂⟩ := h₂
    refine ⟨c₁ * c₂, c₂ • x₁ + c₁ • x₂, by rw [map_mul]; exact mul_ne_zero hc₁ hc₂, ?_⟩
    rw [fibreElt_add, fibreElt_smul, fibreElt_smul, ← h₁, ← h₂, smul_smul, smul_smul, map_mul,
      smul_add, mul_comm (ι c₂) (ι c₁)]
  | smul k w _ h =>
    obtain ⟨c, x, hc, h⟩ := h
    obtain ⟨a, d, hd, hk⟩ := hfrac k
    refine ⟨d * c, a • x, by rw [map_mul]; exact mul_ne_zero hd hc, ?_⟩
    rw [fibreElt_smul, ← h, map_mul, smul_smul, smul_smul, ← hk]
    congr 1
    ring

variable [IsDomain A] [ValuationRing A]

/-- Over a valuation ring, a nonzero element `x` of a finite free module is a nonzero multiple
`a • x'` of an element `x'` not in `𝔪 M`. -/
private theorem exists_eq_smul_notMem_of_valuationRing {M : ModuleCat.{u} A} {n : ℕ}
    (e₀ : M ≅ ModuleCat.of A (ULift.{u} (Fin n → A))) {x : M} (hx0 : x ≠ 0) :
    ∃ (a : A) (x' : M), a ≠ 0 ∧ x = a • x' ∧
      x' ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
  let y := e₀.hom x
  obtain ⟨j, -, hj⟩ := exists_dvd_forall (Finset.univ : Finset (Fin n))
    (by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
      apply hx0
      apply e₀.toLinearEquiv.injective
      rw [map_zero]
      ext i
      exact (h.false i).elim)
    y.down
  have hj0 : y.down j ≠ 0 := by
    intro h0
    apply hx0
    apply e₀.toLinearEquiv.injective
    rw [map_zero]
    ext i
    obtain ⟨q, hq⟩ := hj i (Finset.mem_univ _)
    show y.down i = 0
    rw [hq, h0, zero_mul]
  choose q hq using fun i => hj i (Finset.mem_univ _)
  let x' : M := e₀.inv (ULift.up q)
  have hinv : e₀.hom x' = ULift.up q := by
    rw [← ModuleCat.comp_apply, e₀.inv_hom_id, ModuleCat.id_apply]
  refine ⟨y.down j, x', hj0, ?_, fun hmem => ?_⟩
  · apply e₀.toLinearEquiv.injective
    show e₀.hom x = e₀.hom (y.down j • x')
    rw [map_smul, hinv]
    ext i
    exact hq i
  have hmap : e₀.hom x' ∈ IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A (ULift.{u} (Fin n → A))) := by
    refine Submodule.smul_induction_on hmem (fun a ha m _ => ?_) (fun m₁ m₂ h₁ h₂ => ?_)
    · show e₀.hom (a • m) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [map_add]
      exact Submodule.add_mem _ h₁ h₂
  have hcoord : ∀ w ∈ IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A (ULift.{u} (Fin n → A))), w.down j ∈ IsLocalRing.maximalIdeal A := by
    intro w hw
    refine Submodule.smul_induction_on hw (fun a ha m _ => ?_) (fun m₁ m₂ h₁ h₂ => ?_)
    · show a * m.down j ∈ _
      exact Ideal.mul_mem_right _ _ ha
    · show m₁.down j + m₂.down j ∈ _
      exact Ideal.add_mem _ h₁ h₂
  have hx'j : (e₀.hom x').down j = q j := congrArg (fun w => w.down j) hinv
  have := hcoord _ hmap
  rw [hx'j, (mul_right_eq_self₀.1 (hq j).symm).resolve_right hj0] at this
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 this)

/-- **A degree-zero cycle outside the maximal-ideal multiple, over a valuation ring.** Let `F` be
a complex over a valuation ring `A` with `F⁰` and `F¹` finite free, and let `ι : A ⟶ K` be an
injective map to a field every element of which is a fraction of elements of `A`. If the
generic fibre `F ⊗_A K` has a nonzero degree-zero cycle, then `F` has a degree-zero cycle not
in `𝔪 F⁰`. -/
theorem exists_cycle_notMem_of_valuationRing {K : Type u} [Field K] (ι : A →+* K)
    (hι : Function.Injective ι) (hfrac : ∀ k : K, ∃ a c : A, ι c ≠ 0 ∧ k * ι c = ι a)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) {n : ℕ}
    (e₀ : F.X 0 ≅ ModuleCat.of A (ULift.{u} (Fin n → A))) [Module.Free A (F.X 1)]
    (hgen : ∃ v : (fibreComplex ι F).X 0, v ≠ 0 ∧ (fibreComplex ι F).d 0 1 v = 0) :
    ∃ z : F.X 0, F.d 0 1 z = 0 ∧ z ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (F.X 0)) := by
  obtain ⟨v, hv0, hv⟩ := hgen
  obtain ⟨c, x, hc, hx⟩ := exists_smul_eq_fibreElt_of_forall_fraction ι hfrac (F.X 0) v
  have hfree0 : Module.Free A (F.X 0) := Module.Free.of_equiv e₀.toLinearEquiv.symm
  have hdx : F.d 0 1 x = 0 := by
    refine (fibreElt_eq_zero_iff_of_injective ι hι (F.X 1) _).1 ?_
    rw [← map_fibreElt, ← hx]
    show ((fibreComplex ι F).d 0 1).hom (ι c • v) = 0
    rw [map_smul]
    show ι c • ((fibreComplex ι F).d 0 1) v = 0
    rw [hv, smul_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hv0
    have : ι c • v = 0 := hx.trans (TensorProduct.tmul_zero _ _)
    exact (smul_eq_zero.1 this).resolve_left hc
  obtain ⟨a, x', ha, hxx', hx'⟩ := exists_eq_smul_notMem_of_valuationRing e₀ hx0
  refine ⟨x', (fibreElt_eq_zero_iff_of_injective ι hι (F.X 1) _).1 ?_, hx'⟩
  have h1 : ι a • fibreElt ι (F.X 1) (F.d 0 1 x') = 0 := by
    rw [← fibreElt_smul, ← map_smul, ← hxx', hdx]
    exact TensorProduct.tmul_zero _ _
  exact (smul_eq_zero.1 h1).resolve_left (fun h => ha (hι (h.trans (map_zero ι).symm)))

/-- **A degree-zero lift over a valuation ring.** Let `M ∈ D(A)` be pseudo-coherent, `A` a
valuation ring, let `χ : A ⟶ L` be a local homomorphism to a field and `ι : A ⟶ K` an injective
homomorphism to a field every element of which is a fraction of elements of `A` (for instance the
fraction field). If some map `K[0] ⟶ M ⊗ᴸ K` is nonzero, then some map `A[0] ⟶ M` has nonzero
image under derived extension of scalars along `χ`. -/
theorem exists_unit_map_ne_zero_of_valuationRing {L : Type u} [Field L]
    {χ : A →+* L} [IsLocalHom χ] (Dχ : TotalDerivedExtensionScalars.{u, u, u} χ)
    {K : Type u} [Field K] {ι : A →+* K} (hι : Function.Injective ι)
    (hfrac : ∀ k : K, ∃ a c : A, ι c ≠ 0 ∧ k * ι c = ι a)
    (Dι : TotalDerivedExtensionScalars.{u, u, u} ι)
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M)
    (hgen : ∃ y : DerivedCategory.Q.obj (unitComplex K) ⟶ Dι.functor.obj M, y ≠ 0) :
    ∃ y : DerivedCategory.Q.obj (unitComplex A) ⟶ M, Dχ.functor.map y ≠ 0 := by
  classical
  obtain ⟨P, b, _, _, r, hX, hH, ⟨e⟩⟩ := exists_model M hM
  obtain ⟨e₀⟩ := hX 0
  have hfree1 : Module.Free A (P.X 1) := Module.Free.of_equiv (hX 1).some.toLinearEquiv.symm
  have hgen' : ∃ v : (fibreComplex ι P).X 0, v ≠ 0 ∧ (fibreComplex ι P).d 0 1 v = 0 := by
    obtain ⟨y, hy⟩ := hgen
    have := Dι.comparison_isIso_of_projective P b
    have : (unitComplex K).IsStrictlyLE 0 := isStrictlyLE_unitComplex K
    have := projective_unitComplex_X (R := K)
    have : (unitComplex K).IsKProjective := CochainComplex.isKProjective_of_projective _ 0
    obtain ⟨yt, hyt⟩ := CochainComplex.IsKProjective.Q_map_surjective (unitComplex K)
      (fibreComplex ι P) (y ≫ (Dι.functor.mapIso e.symm).hom ≫ Dι.comparison.app P)
    refine ⟨yt.f 0 (unitGen K), fun h0 => hy ?_, ?_⟩
    · have hyt0 : yt = 0 := isCyclicInDegreeZero_unitComplex.hom_ext (by
        rw [h0]; rfl)
      rw [hyt0, Functor.map_zero] at hyt
      rw [← cancel_mono ((Dι.functor.mapIso e.symm).hom ≫ Dι.comparison.app P), zero_comp]
      exact hyt.symm
    · have := congrArg (fun φ => φ.hom (unitGen K)) (yt.comm 0 1)
      change ((fibreComplex ι P).d 0 1) (yt.f 0 (unitGen K)) =
        yt.f 1 ((unitComplex K).d 0 1 (unitGen K)) at this
      rw [this, HomologicalComplex.single_obj_d]
      exact map_zero _
  obtain ⟨z, hz0, hzm⟩ := exists_cycle_notMem_of_valuationRing ι hι hfrac P e₀ hgen'
  have hzχ := fibreElt_ne_zero_of_notMem χ e₀ hzm
  exact exists_unit_map_ne_zero_of_cycle Dχ P b r hX hH e z hz0 hzχ

end ValuationRing

end StacksDraft.Perfect.FibreCycleLift

end
