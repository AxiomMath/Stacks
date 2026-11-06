module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.GaloisFixedPoints

/-!
# Fixed `L`-points: a finite level, and transport along an isomorphism of separable closures

Let `J : Spec K ⟶ X` and `Y` finite étale over `X`. The elements of `Gal(L/K)` fixing every
`L`-point of `Y` over `J` contain the fixing group of a finite subextension `E ⊆ L`
(`AlgebraicGeometry.exists_finiteDimensional_forall_mem_fixingSubgroup_spec_comp_eq`): they form an
open set (Tag 03VE) containing `1`. If `K → K'` is a field extension, `L` a separable closure of
`K'` and `ι : L ≃ M` an isomorphism over `K` with a separable closure `M` of `K`, then an element
`σ` of `Gal(L/K')` whose conjugate `ι σ ι⁻¹` fixes every `M`-point of `Y` over `J` fixes every
`L`-point of `Y` over `Spec K' ⟶ Spec K ⟶ X` (`AlgebraicGeometry.spec_comp_eq_of_algEquiv`).
These make the open subgroups controlling a continuous representation independent of the constant
field in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The elements fixing every `L`-point of `Y` over `J` contain the fixing group of a finite
subextension.** -/
theorem exists_finiteDimensional_forall_mem_fixingSubgroup_spec_comp_eq {X : Scheme.{u}}
    [ConnectedSpace X] (K L Ω : Type u) [Field K] [Field L] [Field Ω] [Algebra K L]
    [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] (J : Spec (.of K) ⟶ X) (Y : FiniteEtaleOver X) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧ ∀ σ ∈ E.fixingSubgroup,
      ∀ g : Spec (.of L) ⟶ Y.left,
        g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ J →
          Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g := by
  have hopen := isOpen_setOf_forall_galoisEquivEtaleFundamentalGroup_apply_eq K L Ω
    ((finiteEtaleBaseChange J).obj Y)
  have h1 : (1 : Gal(L/K)) ∈ {σ : Gal(L/K) | ∀ p : (finiteEtaleFiberFunctor
      (algebraicClosureGeometricPoint K Ω)).obj ((finiteEtaleBaseChange J).obj Y),
        (((galoisEquivEtaleFundamentalGroup K L Ω) σ).asIso.app _).hom p = p} := by
    intro p
    rw [map_one]
    rfl
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K L _).1 (hopen.mem_nhds h1)
  exact ⟨E, hE, fun σ hσ => forall_spec_comp_eq_of_forall_apply_eq K L Ω J Y σ (hsub hσ)⟩

/-- **Transport of fixed points along an isomorphism of separable closures.** -/
theorem spec_comp_eq_of_algEquiv {X : Scheme.{u}} {K M K' L : Type u} [Field K] [Field M]
    [Field K'] [Field L] [Algebra K M] [Algebra K K'] [Algebra K' L] [Algebra K L]
    [IsScalarTower K K' L] (ι : L ≃ₐ[K] M) (J : Spec (.of K) ⟶ X) (Y : FiniteEtaleOver X)
    (σ : Gal(L/K')) (σ₀ : Gal(M/K)) (hσ₀ : ∀ z, σ₀ (ι z) = ι (σ z))
    (h₀ : ∀ g : Spec (.of M) ⟶ Y.left,
      g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K M)) ≫ J →
        Spec.map (CommRingCat.ofHom σ₀.toAlgHom.toRingHom) ≫ g = g)
    (g : Spec (.of L) ⟶ Y.left)
    (hg : g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K' L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ J) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g := by
  let sι : Spec (.of M) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom ι.toAlgHom.toRingHom)
  have hinv : Spec.map (CommRingCat.ofHom ι.symm.toAlgHom.toRingHom) ≫ sι = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext z
    exact ι.symm_apply_apply z
  have hpt : (sι ≫ g) ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K M)) ≫ J := by
    rw [Category.assoc, hg, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext z
    change ι (algebraMap K' L (algebraMap K K' z)) = algebraMap K M z
    rw [← IsScalarTower.algebraMap_apply]
    exact ι.commutes z
  have h1 := h₀ _ hpt
  have hcomm : Spec.map (CommRingCat.ofHom σ₀.toAlgHom.toRingHom) ≫ sι =
      sι ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext z
    exact hσ₀ z
  rw [← Category.assoc, hcomm, Category.assoc] at h1
  simpa only [← Category.assoc, hinv, Category.id_comp] using
    Spec.map (CommRingCat.ofHom ι.symm.toAlgHom.toRingHom) ≫= h1

end AlgebraicGeometry

end
