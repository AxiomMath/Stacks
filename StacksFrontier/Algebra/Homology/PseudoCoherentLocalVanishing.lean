module

public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalProperties.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Tor.DerivedTensorInvertibleScalar
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayama
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# Local vanishing of a pseudo-coherent complex killed by a Koszul object

Let `R` be a commutative ring, `𝔭 ⊆ R` a prime ideal and `M` a pseudo-coherent object of `D(R)`.
Let `N(a₁, …, aᵣ)` be the object of `D(R)` built from `R[0]` by taking, for each `aᵢ`, a cone of
multiplication by `aᵢ` (a Koszul object). If every `aᵢ` lies in `𝔭` and
`M ⊗ᴸ_R N(a₁, …, aᵣ) = 0`, then every cohomology module of `M` vanishes at `𝔭`: each element of
`Hⁱ(M)` is killed by an element outside `𝔭`.

The proof descends the list. For a pseudo-coherent `C` and `a ∈ 𝔭`, a distinguished triangle
`C --a--> C ⟶ C' ⟶ C[1]` with `C'` vanishing at `𝔭` makes multiplication by `a` surjective on
`Hⁱ(C)_𝔭`, and then `Hⁱ(C)_𝔭 = 0` by Nakayama's lemma on the highest nonzero cohomology of the
pseudo-coherent complex `C ⊗_R R_𝔭` over the local ring `R_𝔭`.

## Main definitions

* `StacksDraft.PseudoCoherence.iteratedSmulCone`: the Koszul object `N(a₁, …, aᵣ)`.

## Main results

* `StacksDraft.PseudoCoherence.isZero_homology_of_forall_surjective_smul`: over a local ring, a
  pseudo-coherent object on whose cohomology a non-unit acts surjectively is zero.
* `StacksDraft.PseudoCoherence.exists_smul_eq_zero_of_isPseudoCoherent`: the same at a prime of
  any ring, for the localized cohomology.
* `StacksDraft.PseudoCoherence.exists_smul_eq_zero_of_isZero_tensor_iteratedSmulCone`: the main
  statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] DerivedCategory.homologyFunctor_linear

universe u

namespace StacksDraft.PseudoCoherence

/-! ### Nakayama's lemma over a local ring -/

/-- **A pseudo-coherent object over a local ring on whose cohomology a non-unit acts surjectively
is zero.** Its highest nonzero cohomology module would be finite and equal to `a` times itself. -/
theorem isZero_homology_of_forall_surjective_smul {S : Type u} [CommRing S] [IsLocalRing S]
    [HasDerivedCategory (ModuleCat.{u} S)]
    {C : DerivedCategory (ModuleCat.{u} S)} (hC : IsPseudoCoherent C) {a : S}
    (ha : a ∈ IsLocalRing.maximalIdeal S)
    (h : ∀ (i : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj C),
      ∃ x, y = a • x) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj C) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hC
  obtain ⟨b, hb⟩ := hE.upperBound
  have : C.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e b
  have hstep : ∀ k : ℕ, ∀ i : ℤ, b - k < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj C) := by
    intro k
    induction k with
    | zero => exact fun i hi => DerivedCategory.isZero_of_isLE C b i (by simpa using hi)
    | succ k ih =>
      intro i hi
      by_cases hik : b - k < i
      · exact ih i hik
      · obtain rfl : i = b - k := by push_cast at hi; omega
        obtain ⟨P, α, hP, hPle, hα⟩ := exists_finiteFree_representative_le C _ ⟨E, hE, ⟨e⟩⟩ ih
        let φ := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) (b - k)).app P).symm ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} S) (b - k)).mapIso (asIso α)
        have hfin : Module.Finite S
            ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) (b - k)).obj
              P) :=
          CochainComplex.finite_homology_of_finiteFree P (b - k) (b - k)
            (fun j => ⟨(hP j).2, (hP j).1⟩)
            fun j hj => ((ih j hj).of_iso
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) j).mapIso (asIso α))).of_iso
              ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) j).app P).symm
        let Hm := (DerivedCategory.homologyFunctor (ModuleCat.{u} S) (b - k)).obj C
        have : Module.Finite S Hm := Module.Finite.equiv φ.toLinearEquiv
        have htop : (⊤ : Submodule S Hm) = ⊥ := by
          refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {a}) ⊤
            Module.Finite.fg_top (fun y _ => ?_) ?_
          · obtain ⟨x, rfl⟩ := h _ y
            exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top
          · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
              Set.singleton_subset_iff]
            exact ha
        have : Subsingleton Hm := subsingleton_of_forall_eq 0 fun y =>
          (Submodule.mem_bot S).1 (htop ▸ Submodule.mem_top)
        exact ModuleCat.isZero_of_subsingleton _
  exact hstep (b - i + 1).toNat i (by omega)

/-! ### Localizing at a prime -/

section Prime

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]

/-- Extension of scalars to `R_𝔭` is additive and exact. -/
private theorem extendScalars_localizationAtPrime_exact :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.AtPrime p))).Additive ∧
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.AtPrime p))) ∧
    PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.AtPrime p))) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.AtPrime p))
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap R (Localization.AtPrime p))).leftAdjoint_preservesColimits
  exact ⟨extendScalars_additive.{u, u, u} _,
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.AtPrime p) p.primeCompl)),
    PreservesColimitsOfSize.preservesFiniteColimits F⟩

/-- Multiplication by `a ∈ R` is surjective on `R_𝔭 ⊗_R G` when it is surjective on `G` up to
elements outside `𝔭`. -/
private theorem exists_tensor_eq_smul {G : Type u} [AddCommGroup G] [Module R G] (a : R)
    (h : ∀ y : G, ∃ (s : R) (x : G), s ∉ p ∧ s • y = a • x)
    (z : TensorProduct R (Localization.AtPrime p) G) :
    ∃ w, z = algebraMap R (Localization.AtPrime p) a • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, (smul_zero _).symm⟩
  | tmul t y =>
    obtain ⟨s, x, hs, hsx⟩ := h y
    let Sp := Localization.AtPrime p
    have v : IsUnit (algebraMap R Sp s) :=
      IsLocalization.map_units Sp (⟨s, show s ∈ p.primeCompl from hs⟩ : p.primeCompl)
    let c : Sp := t * ↑v.unit⁻¹
    have hv : (↑v.unit⁻¹ : Sp) * algebraMap R Sp s = 1 := v.val_inv_mul
    have hc : s • c = t := by
      rw [Algebra.smul_def]
      calc algebraMap R Sp s * (t * ↑v.unit⁻¹) = t * (↑v.unit⁻¹ * algebraMap R Sp s) := by ring
        _ = t := by rw [hv, mul_one]
    refine ⟨c ⊗ₜ x, ?_⟩
    calc t ⊗ₜ[R] y = (s • c) ⊗ₜ[R] y := by rw [hc]
      _ = c ⊗ₜ[R] (s • y) := TensorProduct.smul_tmul _ _ _
      _ = c ⊗ₜ[R] (a • x) := by rw [hsx]
      _ = (a • c) ⊗ₜ[R] x := (TensorProduct.smul_tmul _ _ _).symm
      _ = algebraMap R Sp a • (c ⊗ₜ[R] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨w₁, rfl⟩ := h₁
    obtain ⟨w₂, rfl⟩ := h₂
    exact ⟨w₁ + w₂, (smul_add _ _ _).symm⟩

variable [HasDerivedCategory (ModuleCat.{u} R)]

/-- **The cohomology of a pseudo-coherent object vanishes at `𝔭` when an element of `𝔭` acts on
it surjectively at `𝔭`.** Let `T` be pseudo-coherent in `D(R)` and `a ∈ 𝔭`, such that every
`y ∈ Hⁱ(T)` satisfies `s y = a x` for some `x` and some `s ∉ 𝔭`. Then every element of every
`Hⁱ(T)` is killed by an element outside `𝔭`: Nakayama's lemma on `T ⊗_R R_𝔭`. -/
theorem exists_smul_eq_zero_of_isPseudoCoherent {T : DerivedCategory (ModuleCat.{u} R)}
    (hT : IsPseudoCoherent T) {a : R} (ha : a ∈ p)
    (h : ∀ (i : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj T),
      ∃ (s : R) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj T),
        s ∉ p ∧ s • y = a • x)
    (i : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj T) :
    ∃ s : R, s ∉ p ∧ s • y = 0 := by
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Localization.AtPrime p))
  obtain ⟨E, hE, ⟨e⟩⟩ := hT
  obtain ⟨hadd, hlim, hcolim⟩ := extendScalars_localizationAtPrime_exact p
  let Sp := Localization.AtPrime p
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R Sp)
  -- the cohomology of `T` is that of `E`
  let eT : ∀ j : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj T ≅ E.homology j :=
    fun j => (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).app E
  -- the localized complex and its cohomology
  let E' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  let eS : ∀ j : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} Sp) j).obj
      (DerivedCategory.Q.obj E') ≅ ModuleCat.of Sp (TensorProduct R Sp (E.homology j)) :=
    fun j => (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} Sp) j).app E' ≪≫
      (mapHomologicalComplexCompHomologyFunctorIso F j).app E ≪≫ extendScalarsTensorIso _
  have hE' : IsPseudoCoherent (DerivedCategory.Q.obj E') := by
    obtain ⟨b, hb⟩ := hE.upperBound
    refine ⟨E', ⟨⟨b, ?_⟩, fun j => ?_⟩, ⟨Iso.refl _⟩⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      intro j hj
      exact F.map_isZero (E.isZero_of_isStrictlyLE b j hj)
    · have := (hE.finiteFree j).1
      have := (hE.finiteFree j).2
      exact ⟨Module.Finite.equiv (extendScalarsTensorIso (S := Sp) (E.X j)).symm.toLinearEquiv,
        Module.Free.of_equiv (extendScalarsTensorIso (S := Sp) (E.X j)).symm.toLinearEquiv⟩
  have hz := isZero_homology_of_forall_surjective_smul hE'
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff Sp p a).2 ha) (fun j y => by
      let φ := (eT j).toLinearEquiv
      let ψ := (eS j).toLinearEquiv
      obtain ⟨w, hw⟩ := exists_tensor_eq_smul p a (fun y' => by
          obtain ⟨s, x, hs, hsx⟩ := h j (φ.symm y')
          refine ⟨s, φ x, hs, ?_⟩
          have := congrArg φ hsx
          rwa [map_smul, map_smul, LinearEquiv.apply_symm_apply] at this)
        (ψ y)
      refine ⟨ψ.symm w, ψ.injective ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact hw) i
  have hsub : Subsingleton (TensorProduct R Sp (E.homology i)) :=
    ModuleCat.subsingleton_of_isZero (hz.of_iso (eS i).symm)
  have hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R Sp (E.homology i) 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl Sp _).2 (TensorProduct.isBaseChange R _ Sp)
  let φ := (eT i).toLinearEquiv
  obtain ⟨⟨s, hs⟩, hsy⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (TensorProduct.mk R Sp (E.homology i) 1) (m := φ y)).1 (Subsingleton.elim _ _)
  refine ⟨s, hs, φ.injective ?_⟩
  rw [map_smul, map_zero]
  exact hsy

omit [p.IsPrime] in
/-- **A triangle of multiplication by `a` with third vertex vanishing at `𝔭`.** For a
distinguished triangle `C --a--> C ⟶ C' ⟶ C[1]` in which every element of every `Hⁱ(C')` is
killed by an element outside `𝔭`, every `y ∈ Hⁱ(C)` satisfies `s y = a x` with `s ∉ 𝔭`. -/
theorem exists_smul_eq_smul_of_distTriang {C C' : DerivedCategory (ModuleCat.{u} R)} (a : R)
    (g : C ⟶ C') (k : C' ⟶ C⟦(1 : ℤ)⟧) (hT : Triangle.mk (a • 𝟙 C) g k ∈ distTriang _)
    (h : ∀ (i : ℤ) (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj C'),
      ∃ s : R, s ∉ p ∧ s • z = 0)
    (i : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj C) :
    ∃ (s : R) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj C),
      s ∉ p ∧ s • y = a • x := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) i
  obtain ⟨s, hs, hsy⟩ := h i ((H.map g).hom y)
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (DerivedCategory.HomologySequence.exact₂ _ hT i) (s • y) (by
      change (H.map g).hom (s • y) = 0
      rw [map_smul]
      exact hsy)
  refine ⟨s, x, hs, ?_⟩
  rw [← hx]
  change (H.map (a • 𝟙 C)).hom x = a • x
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end Prime

/-! ### Koszul objects -/

section Koszul

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]

/-- **The Koszul object of a list of elements of `R`**: `R[0]` for the empty list, and a cone of
multiplication by `a` on the Koszul object of `l` for `a :: l`. -/
def iteratedSmulCone : List R → DerivedCategory (ModuleCat.{u} R)
  | [] => (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R)
  | a :: l => (distinguished_cocone_triangle (a • 𝟙 (iteratedSmulCone l))).choose

/-- The distinguished triangle `N(l) ⟶ N(l) ⟶ N(a :: l) ⟶ N(l)[1]` defining a Koszul object. -/
theorem exists_distTriang_iteratedSmulCone_cons (a : R) (l : List R) :
    ∃ (g : iteratedSmulCone l ⟶ iteratedSmulCone (a :: l))
      (k : iteratedSmulCone (a :: l) ⟶ (iteratedSmulCone l)⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (iteratedSmulCone l)) g k ∈ distTriang _ :=
  (distinguished_cocone_triangle (a • 𝟙 (iteratedSmulCone l))).choose_spec

/-- **`R[0]` is perfect**: it is a complex of finite free modules in degree zero. -/
theorem isPerfect_singleFunctor_obj_self :
    StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) := by
  classical
  let P := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of R R)
  have hX : ∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i) := fun i => by
    by_cases hi : i = 0
    · subst hi
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).symm
      exact ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv⟩
    · have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
      exact ⟨inferInstance, Module.Projective.of_free⟩
  exact ⟨P, 0, 0, inferInstance, inferInstance, fun i => (hX i).1, fun i => (hX i).2,
    ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app _⟩⟩

/-- **Koszul objects are perfect.** -/
theorem isPerfect_iteratedSmulCone :
    ∀ l : List R, StacksDraft.Perfect.IsPerfect (iteratedSmulCone l)
  | [] => isPerfect_singleFunctor_obj_self
  | a :: l => by
    obtain ⟨g, k, hT⟩ := exists_distTriang_iteratedSmulCone_cons a l
    exact (StacksDraft.Perfect.isPerfect_of_distinguished _ hT).1 (isPerfect_iteratedSmulCone l)
      (isPerfect_iteratedSmulCone l)

/-- If `c` kills the composites `C ⟶ Z ⟶ Z` and `Z ⟶ C[1] ⟶ C[1]` through `c • 𝟙` in a
distinguished triangle `C ⟶ C' ⟶ Z ⟶ C[1]`, then `c * c` kills `Z`. -/
theorem mul_self_smul_id_eq_zero_of_distTriang_moduleCat (c : R)
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (h₂ : T.mor₂ ≫ (c • 𝟙 T.obj₃) = 0) (h₃ : T.mor₃ ≫ (c • 𝟙 (T.obj₁⟦(1 : ℤ)⟧)) = 0) :
    (c * c) • 𝟙 T.obj₃ = 0 := by
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₃ _ hT (c • 𝟙 T.obj₃) h₂
  rw [mul_smul]
  calc c • c • 𝟙 T.obj₃ = (c • 𝟙 T.obj₃) ≫ (c • 𝟙 T.obj₃) := by
        rw [Linear.smul_comp, Category.id_comp]
    _ = (T.mor₃ ≫ ψ) ≫ (c • 𝟙 T.obj₃) := by
        nth_rewrite 1 [hψ]
        rfl
    _ = 0 := by
        rw [Category.assoc, Linear.comp_smul, Category.comp_id, ← Category.id_comp ψ,
          ← Linear.smul_comp, ← Category.assoc, h₃, zero_comp]

/-- **Every member of the list kills a power of the Koszul object.** -/
theorem exists_pow_smul_id_iteratedSmulCone_eq_zero :
    ∀ (l : List R) (b : R), b ∈ l → ∃ N : ℕ, b ^ N • 𝟙 (iteratedSmulCone l) = 0
  | [], _, hb => absurd hb List.not_mem_nil
  | a :: l, b, hb => by
    obtain ⟨g, k, hT⟩ := exists_distTriang_iteratedSmulCone_cons a l
    have hcone : ∀ c : R, c • 𝟙 (iteratedSmulCone l) = 0 →
        (c * c) • 𝟙 (iteratedSmulCone (a :: l)) = 0 :=
      fun c hc => by
        refine mul_self_smul_id_eq_zero_of_distTriang_moduleCat c _ hT ?_ ?_
        · dsimp only [Triangle.mk_mor₂, Triangle.mk_obj₃]
          rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp g, ← Linear.smul_comp, hc,
            zero_comp]
        · dsimp only [Triangle.mk_mor₃, Triangle.mk_obj₁]
          have : c • 𝟙 ((iteratedSmulCone l)⟦(1 : ℤ)⟧) =
              (shiftFunctor _ (1 : ℤ)).map (c • 𝟙 (iteratedSmulCone l)) := by
            rw [Functor.map_smul, CategoryTheory.Functor.map_id]
          rw [this, hc, Functor.map_zero, comp_zero]
    rcases List.mem_cons.1 hb with rfl | hb
    · refine ⟨2, ?_⟩
      rw [pow_two]
      refine mul_self_smul_id_eq_zero_of_distTriang_moduleCat b _ hT ?_ ?_
      · dsimp only [Triangle.mk_mor₂, Triangle.mk_obj₃]
        rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp g, ← Linear.smul_comp]
        exact comp_distTriang_mor_zero₁₂ _ hT
      · dsimp only [Triangle.mk_mor₃, Triangle.mk_obj₁]
        have : b • 𝟙 ((iteratedSmulCone l)⟦(1 : ℤ)⟧) =
            (shiftFunctor _ (1 : ℤ)).map (b • 𝟙 (iteratedSmulCone l)) := by
          rw [Functor.map_smul, CategoryTheory.Functor.map_id]
        rw [this]
        exact comp_distTriang_mor_zero₃₁ _ hT
    · obtain ⟨N, hN⟩ := exists_pow_smul_id_iteratedSmulCone_eq_zero l b hb
      exact ⟨2 * N, by rw [two_mul, pow_add]; exact hcone _ hN⟩

/-- Every member of the list kills a power of every cohomology module of the Koszul object. -/
theorem exists_pow_smul_homology_iteratedSmulCone_eq_zero (l : List R) (b : R) (hb : b ∈ l) :
    ∃ N : ℕ, ∀ (i : ℤ)
      (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (iteratedSmulCone l)),
      b ^ N • z = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_smul_id_iteratedSmulCone_eq_zero l b hb
  refine ⟨N, fun i z => ?_⟩
  have h0 : (b ^ N) • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (iteratedSmulCone l)) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hN, Functor.map_zero]
  exact congrArg (fun f => f.hom z) h0

/-- Tensoring the defining triangle of `N(a :: l)` with `M` on the left gives a triangle of
multiplication by `a` on `M ⊗ᴸ N(l)`. -/
theorem exists_distTriang_tensor_iteratedSmulCone_cons (M : DerivedCategory (ModuleCat.{u} R))
    (a : R) (l : List R) :
    let F := (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj M
    ∃ (g : F.obj (iteratedSmulCone l) ⟶ F.obj (iteratedSmulCone (a :: l)))
      (k : F.obj (iteratedSmulCone (a :: l)) ⟶ (F.obj (iteratedSmulCone l))⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (F.obj (iteratedSmulCone l))) g k ∈ distTriang _ := by
  intro F
  obtain ⟨g, k, hT⟩ := exists_distTriang_iteratedSmulCone_cons a l
  refine ⟨F.map g, F.map k ≫ (F.commShiftIso (1 : ℤ)).hom.app _,
    isomorphic_distinguished _ (F.map_distinguished _ hT) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)⟩
  · exact (Category.comp_id _).trans
      ((Stacks.DerivedTensor.map_smul_id_right R M _ a).symm.trans (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine Eq.trans ?_ (Category.id_comp _).symm
    exact (congrArg (fun z => _ ≫ z) ((shiftFunctor _ (1 : ℤ)).map_id _)).trans
      (Category.comp_id _)

/-- `M ⊗ᴸ N(l)` is pseudo-coherent when `M` is. -/
theorem isPseudoCoherent_tensor_iteratedSmulCone {M : DerivedCategory (ModuleCat.{u} R)}
    (hM : IsPseudoCoherent M) :
    ∀ l : List R, IsPseudoCoherent
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj M).obj
        (iteratedSmulCone l))
  | [] => hM.ofIso (CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso M).symm
  | a :: l => by
    obtain ⟨g, k, hT⟩ := exists_distTriang_tensor_iteratedSmulCone_cons M a l
    exact isPseudoCoherent_obj₃_of_distinguished _ hT
      (isPseudoCoherent_tensor_iteratedSmulCone hM l)
      (isPseudoCoherent_tensor_iteratedSmulCone hM l)

/-- **A pseudo-coherent complex killed by a Koszul object vanishes at every prime containing the
list.** Let `M` be pseudo-coherent, `l` a list of elements of a prime `𝔭`, and suppose every
element of every cohomology module of `M ⊗ᴸ N(l)` is killed by an element outside `𝔭` (for
instance `M ⊗ᴸ N(l) = 0`). Then every element of every `Hⁱ(M)` is killed by an element outside
`𝔭`. -/
theorem exists_smul_eq_zero_of_tensor_iteratedSmulCone (p : Ideal R) [p.IsPrime]
    {M : DerivedCategory (ModuleCat.{u} R)} (hM : IsPseudoCoherent M) :
    ∀ l : List R, (∀ a ∈ l, a ∈ p) →
      (∀ (i : ℤ) (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj M).obj
            (iteratedSmulCone l))), ∃ s : R, s ∉ p ∧ s • z = 0) →
      ∀ (i : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M),
        ∃ s : R, s ∉ p ∧ s • y = 0
  | [], _, h, i, y => by
    let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso M)
    obtain ⟨s, hs, hsy⟩ := h i (e.toLinearEquiv.symm y)
    refine ⟨s, hs, e.toLinearEquiv.symm.injective ?_⟩
    rw [map_smul, map_zero]
    exact hsy
  | a :: l, hl, h, i, y => by
    obtain ⟨g, k, hT⟩ := exists_distTriang_tensor_iteratedSmulCone_cons M a l
    refine exists_smul_eq_zero_of_tensor_iteratedSmulCone p hM l
      (fun b hb => hl b (List.mem_cons_of_mem a hb)) ?_ i y
    exact exists_smul_eq_zero_of_isPseudoCoherent p (isPseudoCoherent_tensor_iteratedSmulCone hM l)
      (hl a List.mem_cons_self) (exists_smul_eq_smul_of_distTriang p a g k hT h)

/-- **A pseudo-coherent complex `M` with `M ⊗ᴸ N(l) = 0` vanishes at every prime containing `l`**:
every element of every `Hⁱ(M)` is killed by an element outside `𝔭`. -/
theorem exists_smul_eq_zero_of_isZero_tensor_iteratedSmulCone (p : Ideal R) [p.IsPrime]
    {M : DerivedCategory (ModuleCat.{u} R)} (hM : IsPseudoCoherent M) (l : List R)
    (hl : ∀ a ∈ l, a ∈ p)
    (h0 : IsZero (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
      M).obj (iteratedSmulCone l)))
    (i : ℤ) (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) :
    ∃ s : R, s ∉ p ∧ s • y = 0 :=
  exists_smul_eq_zero_of_tensor_iteratedSmulCone p hM l hl (fun j z =>
    ⟨1, p.primeCompl.one_mem, by
      rw [one_smul]
      exact (ModuleCat.subsingleton_of_isZero
        ((DerivedCategory.homologyFunctor _ j).map_isZero h0)).elim _ _⟩) i y

end Koszul

end StacksDraft.PseudoCoherence

end
