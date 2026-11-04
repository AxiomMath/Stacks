module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDualVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSchemeModuleComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightTExactCohomologyClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated

/-!
# A degree-zero presentation of a connective pseudo-coherent complex on an affine scheme

Let `V` be an affine scheme over `S`, regarded as an algebraic space, and let `L` be a
pseudo-coherent object of `D(𝒪_V)` (on the small étale site) with no cohomology in positive
degrees.  Then `H⁰(L)` is a finitely presented module, the cokernel of a map `𝒪ⁿ ⟶ 𝒪ᵐ`, and this
presentation lifts to `D(𝒪_V)`: there are morphisms `eⱼ : 𝒪[0] ⟶ L` and endomorphisms `cᵢⱼ` of
`𝒪[0]` with `∑ⱼ cᵢⱼ ≫ eⱼ = 0` such that, for every `G` with no cohomology in negative degrees,
`γ ↦ (eⱼ ≫ γ)ⱼ` identifies `Hom(L, G)` with the tuples in `Hom(𝒪[0], G)ᵐ` killed by the
relations.  This is Stacks 064U read in degree zero.

The argument models `L` on `V` by a bounded above complex `P` of finite free modules over
`A = Γ(V, 𝒪_V)`, `L ≅ ε^*(P~)`
(`AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso`, through the
étale chart `h_{Spec A} ≅ h_V`, along which derived pullback is an equivalence).  Since the chart
model reflects amplitude, `P` may be taken to vanish in positive degrees (Stacks 064T), so that
`H⁰(P) = Coker(P⁻¹ ⟶ P⁰)` is finitely presented.  Its generators lift to `A[0] ⟶ P`, because
`A[0]` corepresents `H⁰` on `D(A)`, and its relations are multiplications by scalars.  The exact
functor `M ↦ ε^*(M~)` is a left adjoint commuting with cohomology, so it carries this presentation
of `H⁰(P)` to one of `H⁰(L)`; finally, for `X` in degrees `≤ 0` and `G` in degrees `≥ 0`, taking
`H⁰` is a bijection `Hom(X, G) ≅ Hom(H⁰ X, H⁰ G)`.

## Main definitions

* `CategoryTheory.IsRelativePresentation`: morphisms `eⱼ : U ⟶ L` and `cᵢⱼ : U ⟶ U` present `L`
  against a class of test objects.
* `AlgebraicGeometry.Space.IsDegreeZeroPresentation`: the case of `D(𝒪_X)`, `U = 𝒪[0]`, against
  the objects in degrees `≥ 0`.

## Main results

* `AlgebraicGeometry.Space.exists_isDegreeZeroPresentation`: the statement above.
* `AlgebraicGeometry.Space.exists_isDegreeZeroPresentation_chartModelFunctor`: the same for the
  chart model `ε^*(P~)` of a bounded above complex of finite free modules.
* `CategoryTheory.IsRelativePresentation.of_homologyFunctor`: a presentation of `H⁰` against all
  objects is a presentation in `D(𝒜)` against the objects in degrees `≥ 0`.
* `ModuleCat.isRelativePresentation_of_exact`: a right exact sequence `Aˡ ⟶ Aᵏ ⟶ M ⟶ 0`
  presents `M`.

## Implementation notes

The chart model `AlgebraicGeometry.Space.chartModelFunctor` is built at the standard model of the
derived categories involved, so that model is pinned in the section where it is used; at the
default priority the global model of `D(A)` wins and the chart model's statements no longer
elaborate.

## References

* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

/-! ### Presentations relative to a class of test objects -/

namespace CategoryTheory

section RelativePresentation

variable {C : Type*} [Category* C] [Preadditive C]

/-- **A presentation relative to a class `T` of test objects.**  The morphisms `e j : U ⟶ L`
present `L` with relations `c i j : U ⟶ U` against the objects satisfying `T`: the relations
`∑ⱼ cᵢⱼ ≫ eⱼ` vanish, and for every `G` satisfying `T` the map `γ ↦ (eⱼ ≫ γ)ⱼ` from `L ⟶ G` to
`(U ⟶ G)ᵐ` is injective with image the tuples killed by the relations.

Against all objects of an abelian category this says that `L` is the cokernel of the map
`Uⁿ ⟶ Uᵐ` given by the matrix `c`, with the `eⱼ` as the images of the generators. -/
def IsRelativePresentation (T : C → Prop) {U L : C} {m n : ℕ} (e : Fin m → (U ⟶ L))
    (c : Fin n → Fin m → (U ⟶ U)) : Prop :=
  (∀ i, ∑ j, c i j ≫ e j = 0) ∧
  ∀ G : C, T G →
    Function.Injective (fun (γ : L ⟶ G) (j : Fin m) => e j ≫ γ) ∧
    ∀ γ' : Fin m → (U ⟶ G),
      (∀ i, ∑ j, c i j ≫ γ' j = 0) → ∃ γ : L ⟶ G, ∀ j, e j ≫ γ = γ' j

/-- An additive functor carries a vanishing sum of composites to a vanishing sum of composites. -/
private theorem sum_map_comp_eq_zero {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] {X Y Z : C} {m : ℕ} (c : Fin m → (X ⟶ Y)) (e : Fin m → (Y ⟶ Z))
    (h : ∑ j, c j ≫ e j = 0) : ∑ j, F.map (c j) ≫ F.map (e j) = 0 := by
  simp only [← F.map_comp, ← F.map_sum, h, F.map_zero]

namespace IsRelativePresentation

variable {T : C → Prop} {U L : C} {m n : ℕ} {e : Fin m → (U ⟶ L)}
  {c : Fin n → Fin m → (U ⟶ U)}

/-- A relative presentation transported along isomorphisms `U ≅ U'` and `L ≅ L'` compatible with
the generators and with the relations is a relative presentation. -/
theorem of_iso (h : IsRelativePresentation T e c) {U' L' : C} (a : U ≅ U') (b : L ≅ L')
    (e' : Fin m → (U' ⟶ L')) (c' : Fin n → Fin m → (U' ⟶ U'))
    (he : ∀ j, e j ≫ b.hom = a.hom ≫ e' j) (hc : ∀ i j, c i j ≫ a.hom = a.hom ≫ c' i j) :
    IsRelativePresentation T e' c' := by
  have he' : ∀ j, e' j = a.inv ≫ e j ≫ b.hom := fun j => by
    rw [he, Iso.inv_hom_id_assoc]
  have hc' : ∀ i j, c' i j = a.inv ≫ c i j ≫ a.hom := fun i j => by
    rw [hc, Iso.inv_hom_id_assoc]
  refine ⟨fun i => ?_, fun G hG => ⟨fun γ₁ γ₂ hγ => ?_, fun γ' hγ' => ?_⟩⟩
  · simp only [he', hc', Category.assoc, Iso.hom_inv_id_assoc]
    have : ∑ j, a.inv ≫ c i j ≫ e j ≫ b.hom = a.inv ≫ (∑ j, c i j ≫ e j) ≫ b.hom := by
      simp [Preadditive.comp_sum, Preadditive.sum_comp]
    rw [this, h.1 i]
    simp
  · refine (cancel_epi b.hom).1 ((h.2 G hG).1 (funext fun j => ?_))
    have := congrFun hγ j
    simp only [he', Category.assoc] at this
    simpa using (cancel_epi a.inv).1 this
  · obtain ⟨γ, hγ⟩ := (h.2 G hG).2 (fun j => a.hom ≫ γ' j) fun i => by
      simp only [← Category.assoc, hc]
      simp only [Category.assoc]
      rw [← Preadditive.comp_sum, hγ' i, comp_zero]
    refine ⟨b.inv ≫ γ, fun j => ?_⟩
    rw [he', Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hγ j, Iso.inv_hom_id_assoc]

/-- **A relative presentation is reflected by a fully faithful additive functor** carrying the
test objects of the source to test objects of the target. -/
theorem of_fullyFaithful {C' : Type*} [Category* C'] [Preadditive C'] {T' : C' → Prop}
    {Ψ : C ⥤ C'} [Ψ.Additive] (hΨ : Ψ.FullyFaithful) (hT : ∀ G, T G → T' (Ψ.obj G))
    (h : IsRelativePresentation T' (fun j => Ψ.map (e j)) (fun i j => Ψ.map (c i j))) :
    IsRelativePresentation T e c := by
  refine ⟨fun i => hΨ.map_injective ?_, fun G hG => ⟨fun γ₁ γ₂ hγ => ?_, fun γ' hγ' => ?_⟩⟩
  · simpa [Functor.map_sum] using h.1 i
  · refine hΨ.map_injective ((h.2 _ (hT G hG)).1 (funext fun j => ?_))
    simpa using congrArg Ψ.map (congrFun hγ j)
  · obtain ⟨γ, hγ⟩ := (h.2 _ (hT G hG)).2 (fun j => Ψ.map (γ' j)) fun i =>
      sum_map_comp_eq_zero Ψ _ _ (hγ' i)
    refine ⟨hΨ.preimage γ, fun j => hΨ.map_injective ?_⟩
    simpa using hγ j

/-- **A left adjoint carries a presentation against all objects to a presentation against all
objects**: morphisms out of `F L` are morphisms out of `L` into the right adjoint. -/
theorem map_of_adjunction {D : Type*} [Category* D] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C}
    [F.Additive] (adj : F ⊣ G) (h : IsRelativePresentation (fun _ => True) e c) :
    IsRelativePresentation (fun _ => True) (fun j => F.map (e j)) (fun i j => F.map (c i j)) := by
  refine ⟨fun i => ?_, fun N _ => ⟨fun γ₁ γ₂ hγ => ?_, fun γ' hγ' => ?_⟩⟩
  · exact sum_map_comp_eq_zero F _ _ (h.1 i)
  · refine (adj.homEquiv _ _).injective ((h.2 _ trivial).1 (funext fun j => ?_))
    simpa [Adjunction.homEquiv_naturality_left] using congrArg (adj.homEquiv _ _) (congrFun hγ j)
  · let δ : Fin m → (U ⟶ G.obj N) := fun j => adj.homEquiv _ _ (γ' j)
    have hδ : ∀ i, ∑ j, c i j ≫ δ j = 0 := fun i => by
      apply (adj.homEquiv _ _).symm.injective
      have key : ∀ j, F.map (c i j ≫ δ j) ≫ adj.counit.app N = F.map (c i j) ≫ γ' j :=
        fun j => by
          rw [F.map_comp, Category.assoc]
          congr 1
          exact ((adj.homEquiv_counit (g := δ j)).symm.trans
            ((adj.homEquiv _ _).symm_apply_apply (γ' j)))
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, F.map_sum,
        Preadditive.sum_comp, F.map_zero, zero_comp]
      simp only [key]
      exact hγ' i
    obtain ⟨γ, hγ⟩ := (h.2 _ trivial).2 δ hδ
    refine ⟨(adj.homEquiv _ _).symm γ, fun j => ?_⟩
    rw [← Adjunction.homEquiv_naturality_left_symm, hγ j]
    simp [δ]

/-- **A presentation of the cohomology in degree `0` is a presentation in degrees `≥ 0`.**  For
objects `U`, `L` of `D(𝒜)` in degrees `≤ 0`, morphisms `e j : U ⟶ L` and `c i j : U ⟶ U` whose
relations vanish and whose cohomology in degree `0` presents `H⁰(L)` against all objects of `𝒜`
present `L` against the objects in degrees `≥ 0`: for such `G`, taking `H⁰` is a bijection
`Hom(U, G) ≅ Hom(H⁰ U, H⁰ G)` and `Hom(L, G) ≅ Hom(H⁰ L, H⁰ G)`. -/
theorem of_homologyFunctor {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {U L : DerivedCategory A} [U.IsLE 0] [L.IsLE 0] {m n : ℕ} {e : Fin m → (U ⟶ L)}
    {c : Fin n → Fin m → (U ⟶ U)} (hrel : ∀ i, ∑ j, c i j ≫ e j = 0)
    (h : IsRelativePresentation (fun _ => True)
      (fun j => (DerivedCategory.homologyFunctor A 0).map (e j))
      (fun i j => (DerivedCategory.homologyFunctor A 0).map (c i j))) :
    IsRelativePresentation (fun G => G.IsGE 0) e c := by
  refine ⟨hrel, fun G hG => ?_⟩
  have := hG
  have bL := DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE L G 0
  have bU := DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE U G 0
  refine ⟨fun γ₁ γ₂ hγ => bL.1 ((h.2 _ trivial).1 (funext fun j => ?_)), fun γ' hγ' => ?_⟩
  · simpa using congrArg (DerivedCategory.homologyFunctor A 0).map (congrFun hγ j)
  · obtain ⟨γ₀, hγ₀⟩ := (h.2 _ trivial).2 (fun j => (DerivedCategory.homologyFunctor A 0).map
      (γ' j)) fun i => sum_map_comp_eq_zero _ _ _ (hγ' i)
    obtain ⟨γ, rfl⟩ := bL.2 γ₀
    exact ⟨γ, fun j => bU.1 (by simpa using hγ₀ j)⟩

end IsRelativePresentation

end RelativePresentation

end CategoryTheory

/-! ### Finitely presented modules -/

universe w

namespace ModuleCat

open CategoryTheory

variable {A : Type u} [CommRing A]

/-- **A right exact sequence `Aˡ ⟶ Aᵏ ⟶ M ⟶ 0` presents `M`**: the images `f(eⱼ)` of the
standard basis vectors, read as maps `A ⟶ M`, present `M` against all modules, with relations
the coordinates of the images `g(eᵢ)`, read as multiplications `A ⟶ A`. -/
theorem isRelativePresentation_of_exact {M : ModuleCat.{u} A} {k l : ℕ}
    (f : (Fin k → A) →ₗ[A] M) (g : (Fin l → A) →ₗ[A] (Fin k → A))
    (hf : Function.Surjective f) (hfg : Function.Exact g f) :
    IsRelativePresentation (fun _ => True)
      (fun j => ModuleCat.ofHom (LinearMap.toSpanSingleton A M (f (Pi.single j 1))))
      (fun i j => ModuleCat.ofHom (LinearMap.toSpanSingleton A A (g (Pi.single i 1) j))) := by
  have hsum : ∀ x : Fin k → A, ∑ j, x j • (Pi.single j (1 : A) : Fin k → A) = x := fun x => by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hfsum : ∀ x : Fin k → A, ∑ j, x j • f (Pi.single j 1) = f x := fun x => by
    conv_rhs => rw [← hsum x]
    simp [map_sum]
  refine ⟨fun i => ?_, fun N _ => ⟨fun γ₁ γ₂ hγ => ?_, fun γ' hγ' => ?_⟩⟩
  · ext
    simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    rw [hfsum]
    exact (hfg _).2 ⟨_, rfl⟩
  · have hcomp : γ₁.hom ∘ₗ f = γ₂.hom ∘ₗ f := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simpa using congrArg (fun φ => φ.hom (1 : A)) (congrFun hγ j)
    ext m
    obtain ⟨x, rfl⟩ := hf m
    exact LinearMap.congr_fun hcomp x
  · let K : (Fin k → A) →ₗ[A] N := ∑ j, (γ' j).hom ∘ₗ LinearMap.proj j
    have hK : ∀ x, K x = ∑ j, (γ' j).hom (x j) := fun x => by
      simp [K, LinearMap.sum_apply]
    have hKg : ∀ y, K (g y) = 0 := by
      have : K ∘ₗ g = 0 := by
        refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
        have := congrArg (fun φ => φ.hom (1 : A)) (hγ' i)
        simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
          LinearMap.sum_apply, LinearMap.comp_apply,
          LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero,
          LinearMap.zero_apply] at this
        simp [hK, this]
      exact LinearMap.congr_fun this
    have hle : LinearMap.ker f ≤ LinearMap.ker K := fun x hx => by
      obtain ⟨y, rfl⟩ := (hfg x).1 hx
      exact hKg y
    let e := f.quotKerEquivOfSurjective hf
    refine ⟨ModuleCat.ofHom ((LinearMap.ker f).liftQ K hle ∘ₗ e.symm.toLinearMap),
      fun j => ?_⟩
    ext
    have he : e.symm (f (Pi.single j 1)) = Submodule.Quotient.mk (Pi.single j 1) := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, one_smul, LinearEquiv.coe_coe, he,
      Submodule.liftQ_apply, hK]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp

/-- The cohomology in degree `0` of a complex of finite free modules vanishing in positive
degrees is finitely presented: it is the cokernel of the last differential `P⁻¹ ⟶ P⁰`. -/
theorem finitePresentation_homology_zero (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ i, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) (hle : P.IsStrictlyLE 0) :
    Module.FinitePresentation A (P.homology 0) := by
  have hd : P.d 0 1 = 0 := (P.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  let Sc := ShortComplex.mk (P.d (-1) 0) (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)
  have hex : Sc.Exact := ShortComplex.exact_of_g_is_cokernel Sc
    (P.opcyclesIsCokernel (-1) 0 (by simp))
  have := (hP 0).1
  have := (hP 0).2
  have := (hP (-1)).1
  have hsurj : Function.Surjective (P.pOpcycles 0).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hker : (LinearMap.ker (P.pOpcycles 0).hom).FG := by
    rw [← hex.moduleCat_range_eq_ker, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  have : Module.FinitePresentation A (P.opcycles 0) :=
    Module.finitePresentation_of_free_of_surjective _ hsurj hker
  exact Module.FinitePresentation.of_equiv (P.isoHomologyι 0 1 (by simp) hd).symm.toLinearEquiv

/-- **A finitely presented `H⁰` is presented by morphisms out of `A[0]`.**  If the cohomology in
degree `0` of an object `X` of `D(A)` is a finitely presented `A`-module, there are morphisms
`e j : A[0] ⟶ X` and `c i j : A[0] ⟶ A[0]` whose relations vanish in `D(A)` and whose cohomology
in degree `0` presents `H⁰(X)` against all `A`-modules.  The generators lift because `A[0]`
corepresents `H⁰` on `D(A)` (`DerivedCategory.homologyFromSingleAddEquiv`), and the relations are
multiplications by scalars. -/
theorem _root_.DerivedCategory.exists_isRelativePresentation_homologyFunctor_zero
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (X : DerivedCategory (ModuleCat.{u} A))
    [Module.FinitePresentation A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X)] :
    ∃ (m n : ℕ)
      (e : Fin m → ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ X))
      (c : Fin n → Fin m →
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))),
      (∀ i, ∑ j, c i j ≫ e j = 0) ∧
      IsRelativePresentation (fun _ => True)
        (fun j => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (e j))
        (fun i j => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map (c i j)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  obtain ⟨k, l, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' A (H.obj X)
  have hpres := isRelativePresentation_of_exact f g hf hfg
  let s := fun j : Fin k =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton A (H.obj X) (f (Pi.single j 1)))
  let r := fun (i : Fin l) (j : Fin k) =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton A A (g (Pi.single i 1) j))
  let Φ := DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of A A) X 0
  let ι := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
    (ModuleCat.of A A)
  let e := fun j => Φ.symm (s j)
  let c := fun i j => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (r i j)
  have hHe : ∀ j, ι.inv ≫ H.map (e j) = s j := fun j => by
    have := Φ.apply_symm_apply (s j)
    rwa [DerivedCategory.homologyFromSingleAddEquiv_apply] at this
  have hHc : ∀ i j, r i j ≫ ι.inv = ι.inv ≫ H.map (c i j) := fun i j =>
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).inv.naturality
      (r i j))
  refine ⟨k, l, e, c, fun i => Φ.injective ?_, hpres.of_iso ι.symm (Iso.refl _) _ _
    (fun j => by simpa using (hHe j).symm) hHc⟩
  rw [map_sum, map_zero]
  have : ∀ j, Φ (c i j ≫ e j) = r i j ≫ s j := fun j => by
    rw [DerivedCategory.homologyFromSingleAddEquiv_apply, CategoryTheory.Functor.map_comp]
    show ι.inv ≫ H.map (c i j) ≫ H.map (e j) = _
    rw [← Category.assoc, ← hHc, Category.assoc, hHe]
  simp only [this]
  exact hpres.1 i

end ModuleCat

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- `e`, `c` present `L` in degree zero against every object with no cohomology below zero. -/
def IsDegreeZeroPresentation {X : AlgebraicSpaces B S hS} (L : derivedModules B S hS X)
    {m n : ℕ} (e : Fin m → (structureObject B S hS X ⟶ L))
    (c : Fin n → Fin m → (structureObject B S hS X ⟶ structureObject B S hS X)) : Prop :=
  (∀ i, ∑ j, c i j ≫ e j = 0) ∧
  ∀ G : derivedModules B S hS X, G.IsGE 0 →
    Function.Injective (fun (γ : L ⟶ G) (j : Fin m) => e j ≫ γ) ∧
    ∀ γ' : Fin m → (structureObject B S hS X ⟶ G),
      (∀ i, ∑ j, c i j ≫ γ' j = 0) → ∃ γ : L ⟶ G, ∀ j, e j ≫ γ = γ' j

/-! ### The chart model -/

section ChartModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `ε^*` on a represented algebraic space is a left adjoint. -/
instance isLeftAdjoint_representedAssociatedModule (T : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj T)) :
    (representedAssociatedModule B S hS T hF).IsLeftAdjoint :=
  inferInstanceAs (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
      (representedSmallEtaleModuleEquivalence B S hS T).functor).IsLeftAdjoint

/-- The exact functor `M ↦ ε^*(M~)` from `A`-modules to modules on `h_{Spec A}`, of which
`AlgebraicGeometry.Space.chartModelFunctor` is the induced functor on derived categories. -/
abbrev chartModuleFunctor {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (g : B.obj hA ⟶ B.obj hS) :
    ModuleCat.{u} A ⥤ Modules.{u, u} B S hS (yoneda.obj (specFppfOver B S hS hA g))
      (isAlgebraicSpace_yoneda B S hS _) :=
  (tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA g))).hom) ⋙
    representedAssociatedModule B S hS (specFppfOver B S hS hA g) (isAlgebraicSpace_yoneda B S hS _)

attribute [local instance 10000] HasDerivedCategory.standard

variable {B S hS} {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (g : B.obj hA ⟶ B.obj hS)

/-- **The chart model commutes with cohomology**: `Hⁿ(ε^*(K~)) ≅ ε^*(Hⁿ(K)~)`, naturally in
`K ∈ D(A)`, both functors being induced by exact functors. -/
def chartModelFunctorHomologyIso (n : ℤ) :
    chartModelFunctor B S hS hA g ⋙ DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙ chartModuleFunctor B S hS hA g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((representedAssociatedModule B S hS (specFppfOver B S hS hA g)
      (isAlgebraicSpace_yoneda B S hS _)).mapDerivedCategoryHomologyIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA g))).hom
      ).mapDerivedCategoryHomologyIso n) _ ≪≫
    Functor.associator _ _ _

/-- **`M ↦ ε^*(M~)` reflects zero objects**: `M~` is quasi-coherent, `ε^*` is fully faithful on
quasi-coherent modules, and `(-)~` is fully faithful. -/
theorem isZero_of_isZero_chartModuleFunctor_obj (M : ModuleCat.{u} A)
    (h : IsZero ((chartModuleFunctor B S hS hA g).obj M)) : IsZero M := by
  let T := specFppfOver B S hS hA g
  let G₁ := tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj T)).hom
  have hq : (G₁.obj M).IsQuasicoherent := by
    dsimp [G₁]
    infer_instance
  let N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory := ⟨G₁.obj M, hq⟩
  have hN : ∀ f₁ f₂ : G₁.obj M ⟶ G₁.obj M, f₁ = f₂ := fun f₁ f₂ => by
    have := (fullyFaithfulRepresentedAssociatedModuleQcoh B S hS T).map_injective
      (X := N) (Y := N) (f := ObjectProperty.homMk f₁) (g := ObjectProperty.homMk f₂)
      (h.eq_of_src _ _)
    exact congrArg (fun φ => φ.hom) this
  have : (Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj T)).hom).Faithful :=
    Functor.Faithful.of_iso (F := 𝟭 _) Scheme.Modules.restrictFunctorId.symm
  have : (tilde.functor (CommRingCat.of A)).Faithful := tilde.fullyFaithfulFunctor.faithful
  have : G₁.Faithful := Functor.Faithful.comp _ _
  exact (IsZero.iff_id_eq_zero _).2 (G₁.map_injective (hN _ _))

/-- **The chart model reflects cohomological amplitude**: if `ε^*(K~)` lies in degrees `≤ n`, so
does `K`. -/
theorem isLE_of_isLE_chartModelFunctor_obj (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : ((chartModelFunctor B S hS hA g).obj K).IsLE n) : K.IsLE n := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine isZero_of_isZero_chartModuleFunctor_obj hA g _ ?_
  exact (DerivedCategory.isZero_of_isLE _ n i hi).of_iso
    ((chartModelFunctorHomologyIso hA g i).app K).symm

/-- The chart model is additive. -/
instance additive_chartModelFunctor : (chartModelFunctor B S hS hA g).Additive := by
  unfold chartModelFunctor representedDerivedAssociatedModule
  infer_instance

/-- The chart model carries objects in degrees `≤ n` to objects in degrees `≤ n`. -/
theorem isLE_chartModelFunctor_obj (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) [K.IsLE n] :
    ((chartModelFunctor B S hS hA g).obj K).IsLE n := by
  have := Stacks.Homology.isLE_mapDerivedCategory_obj
    (tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
      (Iso.refl ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA g))).hom) K n
  exact Stacks.Homology.isLE_mapDerivedCategory_obj (representedAssociatedModule B S hS
    (specFppfOver B S hS hA g) (isAlgebraicSpace_yoneda B S hS _)) _ n

/-- **Stacks 064U in degree zero, on an affine chart.**  Let `P` be a bounded above complex of
finite free `A`-modules whose chart model `ε^*(P~)` lies in degrees `≤ 0`.  Then `ε^*(P~)` is
presented in degree zero by finitely many morphisms `𝒪[0] ⟶ ε^*(P~)` with relations given by
endomorphisms of `𝒪[0]`, against every object in degrees `≥ 0`.

The chart model reflects amplitude, so `P` may be taken to vanish in positive degrees; then
`H⁰(P)` is the cokernel of `P⁻¹ ⟶ P⁰`, a finitely presented module, presented by morphisms out
of `A[0]`, and the exact functor `M ↦ ε^*(M~)`, a left adjoint commuting with cohomology, carries
this presentation of `H⁰(P)` to one of `H⁰(ε^*(P~))`. -/
theorem exists_isDegreeZeroPresentation_chartModelFunctor (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (hLE : ((chartModelFunctor B S hS hA g).obj (DerivedCategory.Q.obj P)).IsLE 0) :
    ∃ (m n : ℕ) (e : Fin m → (structureObject B S hS (schemeSpace (specFppfOver B S hS hA g)) ⟶
        (chartModelFunctor B S hS hA g).obj (DerivedCategory.Q.obj P)))
      (c : Fin n → Fin m → (structureObject B S hS (schemeSpace (specFppfOver B S hS hA g)) ⟶
        structureObject B S hS (schemeSpace (specFppfOver B S hS hA g)))),
      IsDegreeZeroPresentation B S hS
        ((chartModelFunctor B S hS hA g).obj (DerivedCategory.Q.obj P)) e c := by
  let F := chartModelFunctor B S hS hA g
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let X := DerivedCategory.Q.obj P
  have hX : X.IsLE 0 := isLE_of_isLE_chartModelFunctor_obj hA g X 0 hLE
  obtain ⟨P', α, hP'fin, hP'le, hα⟩ :=
    StacksDraft.PseudoCoherence.IsPseudoCoherentIn.exists_finiteFree_representative_le
      (K := X) ⟨P, hP, ⟨Iso.refl _⟩⟩ 0 fun i hi => DerivedCategory.isZero_of_isLE X 0 i hi
  have : Module.FinitePresentation A (H.obj X) :=
    have := ModuleCat.finitePresentation_homology_zero P' hP'fin hP'le
    Module.FinitePresentation.of_equiv
      ((StacksDraft.PseudoCoherence.homologyQObjIso P' 0).symm ≪≫ H.mapIso (asIso α)).toLinearEquiv
  obtain ⟨m, n, e₀, c₀, hrel₀, hpres₀⟩ :=
    DerivedCategory.exists_isRelativePresentation_homologyFunctor_zero X
  let U₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have : (F.obj U₀).IsLE 0 := isLE_chartModelFunctor_obj hA g U₀ 0
  have : (F.obj X).IsLE 0 := hLE
  let η := chartModelFunctorHomologyIso hA g 0
  have hpres₁ := (hpres₀.map_of_adjunction
    (Adjunction.ofIsLeftAdjoint (chartModuleFunctor B S hS hA g))).of_iso
      (η.app U₀).symm (η.app X).symm (fun j => (DerivedCategory.homologyFunctor _ 0).map
        (F.map (e₀ j))) (fun i j => (DerivedCategory.homologyFunctor _ 0).map (F.map (c₀ i j)))
      (fun j => (η.inv.naturality (e₀ j)).trans rfl)
      (fun i j => (η.inv.naturality (c₀ i j)).trans rfl)
  have hpres₂ : IsRelativePresentation (fun G => G.IsGE 0) (fun j => F.map (e₀ j))
      (fun i j => F.map (c₀ i j)) :=
    IsRelativePresentation.of_homologyFunctor
      (fun i => sum_map_comp_eq_zero F _ _ (hrel₀ i)) hpres₁
  let a : F.obj U₀ ≅ structureObject B S hS (schemeSpace (specFppfOver B S hS hA g)) :=
    chartModelFunctorSingleIso B S hS hA g 0 ≪≫
      (shiftFunctorZero' _ (-0 : ℤ) (by simp)).app _
  exact ⟨m, n, fun j => a.inv ≫ F.map (e₀ j), fun i j => a.inv ≫ F.map (c₀ i j) ≫ a.hom,
    hpres₂.of_iso a (Iso.refl _) _ _
      (fun j => (Category.comp_id _).trans (Iso.hom_inv_id_assoc a _).symm)
      (fun i j => (Iso.hom_inv_id_assoc a _).symm)⟩

end ChartModel

/-- **Stacks 064U in degree zero, on an affine scheme.**  Let `V` be an affine scheme over `S`,
regarded as an algebraic space, and `L` a pseudo-coherent object of `D(𝒪_V)` with no cohomology
in positive degrees.  Then `L` has a degree-zero presentation: finitely many morphisms
`𝒪[0] ⟶ L` with relations given by endomorphisms of `𝒪[0]`, against every object in degrees
`≥ 0`.

Along the étale chart `h_{Spec A} ≅ h_V`, `A = Γ(V, 𝒪_V)`, derived pullback is an equivalence
carrying `L` to the chart model `ε^*(P~)` of a bounded above complex of finite free `A`-modules,
`𝒪` to `𝒪` and objects in degrees `≥ 0` to objects in degrees `≥ 0`; there
`AlgebraicGeometry.Space.exists_isDegreeZeroPresentation_chartModelFunctor` applies. -/
theorem exists_isDegreeZeroPresentation (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (L : derivedModules B S hS ((schemeSpaceFunctor B S hS).obj V))
    (hL : (smallEtaleRingedSite B S hS _ ((schemeSpaceFunctor B S hS).obj V).2).IsPseudoCoherent L)
    (hL0 : L.IsLE 0) :
    ∃ (m n : ℕ) (e : Fin m → (structureObject B S hS _ ⟶ L))
      (c : Fin n → Fin m → (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V) ⟶
        structureObject B S hS _)),
      IsDegreeZeroPresentation B S hS L e c := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  let eX := ((BigFppfOver.toScheme B S hS).obj V).isoSpec
  have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact eX.inv) V.left.2
  let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk eX.inv ≫ V.hom
  let eV : specFppfOver B S hS hA gA ≅ V :=
    Over.isoMk (B.inclusion.preimageIso eX.symm) (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      rfl))
  let Vs := (schemeSpaceFunctor B S hS).obj V
  let Ys : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩
  let φ : Ys ⟶ Vs := representedSpaceMap B S hS eV.hom
  let φ' : Vs ⟶ Ys := representedSpaceMap B S hS eV.inv
  have hφ : IsEtale B S hS φ.hom := isEtale_of_isIso B S hS (yoneda.map eV.hom)
  have h₁ : φ ≫ φ' = 𝟙 Ys := by
    refine ObjectProperty.hom_ext _ ?_
    show yoneda.map eV.hom ≫ yoneda.map eV.inv = 𝟙 _
    rw [← yoneda.map_comp, eV.hom_inv_id, yoneda.map_id]
  have h₂ : φ' ≫ φ = 𝟙 Vs := by
    refine ObjectProperty.hom_ext _ ?_
    show yoneda.map eV.inv ≫ yoneda.map eV.hom = 𝟙 _
    rw [← yoneda.map_comp, eV.inv_hom_id, yoneda.map_id]
  let D := smallEtaleDerivedPullbackData B S hS
  let Ψ := D.pull φ
  let E : derivedModules B S hS Vs ≌ derivedModules B S hS Ys :=
    CategoryTheory.Equivalence.mk Ψ (D.pull φ') ((D.idIso Vs).symm ≪≫ D.triangle h₂)
      ((D.triangle h₁).symm ≪≫ D.idIso Ys)
  have hΨ : Ψ.FullyFaithful := E.fullyFaithfulFunctor
  have : Ψ.Additive := additive_smallEtaleDerivedModulePullback B S hS φ
  let := HasDerivedCategory.standard
    (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA gA φ hφ L hL
  obtain ⟨e₁⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ L
  let uL : Ψ.obj L ≅ (chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P) := e₁.symm ≪≫ eP
  have hLE : ((chartModelFunctor B S hS hA gA).obj (DerivedCategory.Q.obj P)).IsLE 0 := by
    have : (Ψ.obj L).IsLE 0 := isLE_smallEtaleDerivedModulePullback_obj φ L 0 hL0
    exact DerivedCategory.TStructure.t.isLE_of_iso uL 0
  obtain ⟨m, n, e', c', h'⟩ := exists_isDegreeZeroPresentation_chartModelFunctor hA gA P hP hLE
  let uO : Ψ.obj (structureObject B S hS Vs) ≅ structureObject B S hS Ys :=
    smallEtaleDerivedPullStructureIso B S hS φ
  have h'' : IsRelativePresentation (fun G => G.IsGE 0)
      (fun j => uO.hom ≫ e' j ≫ uL.inv) (fun i j => uO.hom ≫ c' i j ≫ uO.inv) :=
    IsRelativePresentation.of_iso h' uO.symm uL.symm _ _
      (fun j => (Iso.inv_hom_id_assoc uO _).symm) (fun i j => (Iso.inv_hom_id_assoc uO _).symm)
  have hGE : ∀ G : derivedModules B S hS Vs, G.IsGE 0 → (Ψ.obj G).IsGE 0 := fun G hG => by
    have := etaleModulePullback_additive.{u, u} B S hS φ hφ
    have := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
    have := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
    obtain ⟨eG⟩ := nonempty_etaleModulePullback_mapDerivedCategory_iso φ hφ G
    have := hG
    have := DerivedCategory.isGE_mapDerivedCategory_obj
      (etaleModulePullback.{u, u} B S hS φ hφ) G 0
    exact DerivedCategory.TStructure.t.isGE_of_iso eG 0
  refine ⟨m, n, fun j => hΨ.preimage (uO.hom ≫ e' j ≫ uL.inv),
    fun i j => hΨ.preimage (uO.hom ≫ c' i j ≫ uO.inv),
    IsRelativePresentation.of_fullyFaithful (T' := fun G => G.IsGE 0) hΨ hGE ?_⟩
  simpa only [Functor.FullyFaithful.map_preimage] using h''

end AlgebraicGeometry.Space

end
