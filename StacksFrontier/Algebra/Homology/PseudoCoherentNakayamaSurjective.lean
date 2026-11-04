module

public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels

/-!
# The derived Nakayama lemma along a surjection

The derived Nakayama lemma of `StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels` is
stated for the reduction `R → R/I` modulo an ideal in the Jacobson radical. This file states it
for an arbitrary surjective ring map `φ : R →+* B` whose kernel lies in the Jacobson radical, in
any models of the derived categories: derived extension of scalars along `φ` detects zero objects
and isomorphisms between pseudo-coherent objects.

## Main results

* `StacksDraft.PseudoCoherence.epi_of_epi_extendScalars_map_of_surjective`: Nakayama's lemma for
  a map onto a finite module.
* `IsPseudoCoherentIn.isZero_of_isZero_totalDerivedExtensionScalars_of_surjective` and
  `IsPseudoCoherentIn.isIso_of_isIso_totalDerivedExtensionScalars_map_of_surjective`, in the
  namespace `StacksDraft.PseudoCoherence`: the derived Nakayama lemma along `φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CochainComplex.DerivedExtensionScalars
open scoped ZeroObject TensorProduct

universe u v wR wA

namespace StacksDraft.PseudoCoherence

/-- **Nakayama's lemma for a map onto a finite module, along a surjection.** If `φ : R →+* B` is
surjective with kernel in the Jacobson radical of `R`, `M` is a finite `R`-module and
`g : N ⟶ M` becomes an epimorphism after extension of scalars to `B`, then `g` is an
epimorphism. -/
theorem epi_of_epi_extendScalars_map_of_surjective {R : Type u} {B : Type u} [CommRing R]
    [CommRing B] {φ : R →+* B} (hφ : Function.Surjective φ)
    (hI : RingHom.ker φ ≤ Ideal.jacobson ⊥) {N M : ModuleCat.{max v u} R} [Module.Finite R M]
    (g : N ⟶ M) (hg : Epi ((ModuleCat.extendScalars.{u, u, max v u} φ).map g)) :
    Epi g := by
  let F := ModuleCat.extendScalars.{u, u, max v u} φ
  let Q : ModuleCat.{max v u} R := ModuleCat.of R (M ⧸ LinearMap.range g.hom)
  let π : M ⟶ Q := ModuleCat.ofHom (LinearMap.range g.hom).mkQ
  have hgπ : g ≫ π = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hFπ : F.map π = 0 := by
    rw [← cancel_epi (F.map g), ← F.map_comp, hgπ, F.map_zero, comp_zero]
  have : Epi π := (ModuleCat.epi_iff_surjective π).2 (Submodule.mkQ_surjective _)
  have hFπepi : Epi (F.map π) := inferInstance
  rw [hFπ] at hFπepi
  have hQ : IsZero (F.obj Q) := IsZero.of_epi_zero (F.obj M) (F.obj Q)
  let Bφ := (ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of B B)
  have hsub : Subsingleton (TensorProduct R Bφ Q) := ModuleCat.subsingleton_of_isZero hQ
  let ℓ₀ : R →ₗ[R] Bφ := LinearMap.toSpanSingleton R Bφ (1 : B)
  have hℓ₀ (x : R) : ℓ₀ x = φ x := mul_one (φ x)
  have hker : RingHom.ker φ ≤ LinearMap.ker ℓ₀ := fun x hx => by rwa [LinearMap.mem_ker, hℓ₀]
  let ℓ : (R ⧸ RingHom.ker φ) →ₗ[R] Bφ := (RingHom.ker φ).liftQ ℓ₀ hker
  have hℓ : Function.Bijective ℓ := by
    refine ⟨?_, fun b => ?_⟩
    · rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rwa [LinearMap.mem_ker, hℓ₀] at hx
    · obtain ⟨x, rfl⟩ := hφ b
      exact ⟨Submodule.Quotient.mk x, hℓ₀ x⟩
  have hsub' : Subsingleton ((R ⧸ RingHom.ker φ) ⊗[R] Q) :=
    (LinearEquiv.rTensor Q (LinearEquiv.ofBijective ℓ hℓ)).toEquiv.injective.subsingleton
  have hquot : Subsingleton (Q ⧸ RingHom.ker φ • (⊤ : Submodule R Q)) :=
    (TensorProduct.quotTensorEquivQuotSMul Q (RingHom.ker φ)).toEquiv.surjective.subsingleton
  have hz : (⊤ : Submodule R Q) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (RingHom.ker φ) ⊤ Module.Finite.fg_top
      (Submodule.Quotient.subsingleton_iff.mp hquot).ge hI
  have : Subsingleton Q := (Submodule.subsingleton_iff R).1 (subsingleton_iff_bot_eq_top.1 hz.symm)
  exact (ModuleCat.epi_iff_surjective g).2
    (LinearMap.range_eq_top.1 (Submodule.Quotient.subsingleton_iff.1 this))

section ExtensionScalars

variable {R : Type u} {B : Type u} [CommRing R] [CommRing B] {φ : R →+* B}
  [HasDerivedCategory.{wR} (ModuleCat.{max v u} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} B)]

/-- **One step of the derived Nakayama lemma**, in any models. Let `φ : R →+* B` be
surjective with kernel in the Jacobson radical of `R` and let `C` be pseudo-coherent with no
cohomology above degree `n`. If the derived reduction `C ⊗ᴸ_R B` vanishes, then so does
`Hⁿ(C)`. -/
theorem IsPseudoCoherentIn.isZero_homology_of_isZero_totalDerivedExtensionScalars_of_surjective
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} φ)
    {C : DerivedCategory (ModuleCat.{max v u} R)} (hC : IsPseudoCoherentIn C)
    (hDq : IsZero (Dq.functor.obj C)) (n : ℤ)
    (hvan : ∀ i, n < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj C) := by
  obtain ⟨P, α, hP, hPle, hα⟩ := hC.exists_finiteFree_representative_le n hvan
  have : ∀ i, Projective (P.X i) := fun i => by
    have := (hP i).2
    infer_instance
  have := Dq.comparison_isIso_of_projective P n
  let F := ModuleCat.extendScalars.{u, u, max v u} φ
  let FP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  -- `C ⊗ᴸ_R B` is computed by the degreewise reduction `FP` of `P`.
  let e : DerivedCategory.Q.obj FP ≅ Dq.functor.obj C :=
    (asIso (Dq.comparison.app P)).symm ≪≫ Dq.functor.mapIso (asIso α)
  have hFP : IsZero (FP.homology n) :=
    ((DerivedCategory.homologyFunctor _ n).map_isZero (hDq.of_iso e)).of_iso
      (homologyQObjIso FP n).symm
  have hP1 : IsZero (P.X (n + 1)) := P.isZero_of_isStrictlyLE n (n + 1) (by omega)
  have := (hP n).1
  have hPn : IsZero (P.homology n) := (isZero_homology_iff_epi_d_of_isZero P n hP1).2
    (epi_of_epi_extendScalars_map_of_surjective hφ hI _
      ((isZero_homology_iff_epi_d_of_isZero FP n (F.map_isZero hP1)).1 hFP))
  exact (hPn.of_iso (homologyQObjIso P n)).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso (asIso α)).symm

/-- **Derived Nakayama lemma along a surjection**, in any models. Let `φ : R →+* B` be surjective
with kernel in the Jacobson radical of `R`. A pseudo-coherent object `C` of `D(R)` whose derived
extension of scalars `C ⊗ᴸ_R B` vanishes is zero. -/
theorem IsPseudoCoherentIn.isZero_of_isZero_totalDerivedExtensionScalars_of_surjective
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} φ)
    {C : DerivedCategory (ModuleCat.{max v u} R)} (hC : IsPseudoCoherentIn C)
    (hDq : IsZero (Dq.functor.obj C)) :
    IsZero C := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hC
  obtain ⟨b, hb⟩ := hE.upperBound
  have : C.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e b
  have hstep : ∀ k : ℕ, ∀ i : ℤ, b - k < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C) := by
    intro k
    induction k with
    | zero => exact fun i hi => DerivedCategory.isZero_of_isLE C b i (by simpa using hi)
    | succ k ih =>
      intro i hi
      by_cases hik : b - k < i
      · exact ih i hik
      · obtain rfl : i = b - k := by push_cast at hi; omega
        exact
          IsPseudoCoherentIn.isZero_homology_of_isZero_totalDerivedExtensionScalars_of_surjective
          hφ hI Dq ⟨E, hE, ⟨e⟩⟩ hDq _ ih
  have : IsIso (0 : (0 : DerivedCategory (ModuleCat.{max v u} R)) ⟶ C) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    exact ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _)).isIso
      (hstep (b - i + 1).toNat i (by omega)) _
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategory (ModuleCat.{max v u} R)) ⟶ C)).symm

/-- **Derived extension of scalars along a surjection with kernel in the Jacobson radical
detects isomorphisms of pseudo-coherent objects**, in any models. If `f : K ⟶ L` is a morphism of
pseudo-coherent objects of `D(R)` and `f ⊗ᴸ_R B` is an isomorphism, then `f` is an
isomorphism. -/
theorem IsPseudoCoherentIn.isIso_of_isIso_totalDerivedExtensionScalars_map_of_surjective
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} φ)
    {K L : DerivedCategory (ModuleCat.{max v u} R)} (hK : IsPseudoCoherentIn K)
    (hL : IsPseudoCoherentIn L) (f : K ⟶ L) (hf : IsIso (Dq.functor.map f)) :
    IsIso f := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle f
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (IsPseudoCoherentIn.isZero_of_isZero_totalDerivedExtensionScalars_of_surjective hφ hI Dq
      (IsPseudoCoherentIn.obj₃_of_distinguished _ hT hK hL)
      ((Triangle.isZero₃_iff_isIso₁ _ (Dq.functor.map_distinguished _ hT)).2 hf))

end ExtensionScalars

end StacksDraft.PseudoCoherence
