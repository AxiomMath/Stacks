module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived Nakayama lemma for pseudo-coherent complexes

Let `R` be a commutative ring and let `I ⊆ R` be an ideal contained in the Jacobson radical.
Derived reduction modulo `I`, the derived extension of scalars along `R → R/I`, detects
isomorphisms between pseudo-coherent objects of `D(R)`: if `K ⟶ L` is a morphism of
pseudo-coherent objects which becomes an isomorphism after `- ⊗ᴸ_R R/I`, it is an isomorphism.

The proof reduces to objects through the cone, which is again pseudo-coherent. A pseudo-coherent
object `C` is represented by a complex `P` of finite free modules ending in the degree `n` of its
highest cohomology, so that `Hⁿ(C)` is the cokernel of the last differential of `P`; that
complex computes `C ⊗ᴸ_R R/I`, and Nakayama's lemma shows that the last differential is already
surjective when it is so modulo `I`.

## Main results

* `StacksDraft.PseudoCoherence.isPseudoCoherent_totalDerivedExtensionScalars_obj`: derived
  extension of scalars preserves pseudo-coherence.
* `StacksDraft.PseudoCoherence.isPseudoCoherent_obj₃_of_distinguished`: the third object of a
  distinguished triangle on two pseudo-coherent objects is pseudo-coherent.
* `StacksDraft.PseudoCoherence.isZero_of_isZero_derivedExtensionScalars_quotient`: a
  pseudo-coherent object whose derived reduction modulo `I` vanishes is zero.
* `StacksDraft.PseudoCoherence.isIso_of_isIso_derivedExtensionScalars_quotient_map`: derived
  reduction modulo `I` detects isomorphisms between pseudo-coherent objects.
* `StacksDraft.PseudoCoherence.span_singleton_pow_le_jacobson_bot_of_isAdicComplete`: for `R`
  complete with respect to `(p)`, every nonzero power of `p` lies in the Jacobson radical.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CochainComplex.DerivedExtensionScalars
open scoped ZeroObject TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace StacksDraft.PseudoCoherence

/-- Extension of scalars along a ring map is a left adjoint. -/
private theorem isLeftAdjoint_extendScalars {R : Type u} {B : Type w} [CommRing R] [CommRing B]
    (φ : R →+* B) : (ModuleCat.extendScalars.{u, w, max v u w} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{max v u w, u, w} φ).isLeftAdjoint

/-- Derived extension of scalars is computed by a bounded-above complex of free modules. -/
private theorem isIso_comparison_app_of_free {R : Type u} {B : Type w} [CommRing R] [CommRing B]
    {φ : R →+* B} (D : TotalDerivedExtensionScalars.{u, v, w} φ)
    (P : CochainComplex (ModuleCat.{max v u w} R) ℤ) (n : ℤ) [P.IsStrictlyLE n]
    (hP : ∀ i, Module.Free R (P.X i)) : IsIso (D.comparison.app P) :=
  have (i : ℤ) : Projective (P.X i) := have := hP i; inferInstance
  D.comparison_isIso_of_projective P n

/-- Derived extension of scalars along a ring map `φ : R →+* B` sends pseudo-coherent objects to
pseudo-coherent objects: a bounded-above complex `E` of finite free `R`-modules representing `K`
computes the derived functor, and its degreewise extension of scalars is a bounded-above complex
of finite free `B`-modules. -/
theorem isPseudoCoherent_totalDerivedExtensionScalars_obj
    {R : Type u} {B : Type w} [CommRing R] [CommRing B] {φ : R →+* B}
    (D : TotalDerivedExtensionScalars.{u, v, w} φ)
    {K : DerivedCategory (ModuleCat.{max v u w} R)} (hK : IsPseudoCoherent K) :
    IsPseudoCoherent (D.functor.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  have := isIso_comparison_app_of_free D E b fun i => (hE.finiteFree i).2
  have := isLeftAdjoint_extendScalars.{u, v, w} φ
  let F := ModuleCat.extendScalars.{u, w, max v u w} φ
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, ⟨⟨b, ?_⟩, fun i => ?_⟩,
    ⟨(asIso (D.comparison.app E)).symm ≪≫ D.functor.mapIso e⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero (E.isZero_of_isStrictlyLE b i hi)
  · have := (hE.finiteFree i).1
    have := (hE.finiteFree i).2
    let : Algebra R B := φ.toAlgebra
    constructor
    · change Module.Finite B (TensorProduct R B (E.X i))
      infer_instance
    · change Module.Free B (TensorProduct R B (E.X i))
      infer_instance

/-- **Stacks 064V**, the cone case. In a distinguished triangle `K → L → C → K[1]` of `D(R)` whose
first two objects are pseudo-coherent, the third object is pseudo-coherent. -/
@[sga "6 I 2.6" "partial"]
theorem isPseudoCoherent_obj₃_of_distinguished {R : Type u} [Ring R]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distTriang _)
    (h₁ : IsPseudoCoherent T.obj₁) (h₂ : IsPseudoCoherent T.obj₂) :
    IsPseudoCoherent T.obj₃ :=
  (isPseudoCoherent_of_distinguished T hT).1 h₁ h₂

/-- **Nakayama's lemma for a map onto a finite module.** If `I` lies in the Jacobson radical of
`R`, `M` is a finite `R`-module and `g : N ⟶ M` becomes an epimorphism after extension of
scalars to `R ⧸ I`, then `g` is an epimorphism. -/
theorem epi_of_epi_extendScalars_quotient_map {R : Type u} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {N M : ModuleCat.{max v u} R} [Module.Finite R M] (g : N ⟶ M)
    (hg : Epi ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map g)) :
    Epi g := by
  have := isLeftAdjoint_extendScalars.{u, v, u} (Ideal.Quotient.mk I)
  let F := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let Q : ModuleCat.{max v u} R := ModuleCat.of R (M ⧸ LinearMap.range g.hom)
  let π : M ⟶ Q := ModuleCat.ofHom (LinearMap.range g.hom).mkQ
  have hgπ : g ≫ π = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hFπ : F.map π = 0 := by
    rw [← cancel_epi (F.map g), ← F.map_comp, hgπ, F.map_zero, comp_zero]
  have hπepi : Epi π :=
    (ModuleCat.epi_iff_surjective π).2 (Submodule.mkQ_surjective _)
  have hFπepi : Epi (F.map π) := inferInstance
  rw [hFπ] at hFπepi
  have hQ : IsZero (F.obj Q) := IsZero.of_epi_zero (F.obj M) (F.obj Q)
  have hsub : Subsingleton ((R ⧸ I) ⊗[R] Q) := ModuleCat.subsingleton_of_isZero hQ
  have hz : (⊤ : Submodule R Q) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top
      (Submodule.Quotient.subsingleton_iff.mp
        (TensorProduct.quotTensorEquivQuotSMul Q I).toEquiv.surjective.subsingleton).ge hI
  have hrange : LinearMap.range g.hom = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (Submodule.Quotient.mk x : Q) ∈ (⊥ : Submodule R Q) := hz ▸ Submodule.mem_top
    exact (Submodule.Quotient.mk_eq_zero _).1 hx
  exact (ModuleCat.epi_iff_surjective g).2 (LinearMap.range_eq_top.1 hrange)

/-- A complex `P` with `P.X (n + 1) = 0` has vanishing degree-`n` homology exactly when its
differential into degree `n` is an epimorphism. -/
theorem isZero_homology_iff_epi_d_of_isZero {C : Type*} [Category C] [Abelian C]
    (P : CochainComplex C ℤ) (n : ℤ) (hP : IsZero (P.X (n + 1))) :
    IsZero (P.homology n) ↔ Epi (P.d (n - 1) n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' P (n - 1) n (n + 1) (by simp) (by simp)]
  exact ShortComplex.exact_iff_epi _ (hP.eq_of_tgt _ _)

/-- **One step of the derived Nakayama lemma.** Let `I` lie in the Jacobson radical of `R` and
let `C` be a pseudo-coherent object of `D(R)` with no cohomology above degree `n`. If the derived
reduction `C ⊗ᴸ_R R/I` vanishes, then so does `Hⁿ(C)`. -/
theorem isZero_homology_of_isZero_derivedExtensionScalars_quotient
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    {C : DerivedCategory (ModuleCat.{max v u} R)} (hC : IsPseudoCoherent C)
    (hDq : IsZero (Dq.functor.obj C)) (n : ℤ)
    (hvan : ∀ i, n < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj C) := by
  obtain ⟨P, α, hP, hPle, hα⟩ := exists_finiteFree_representative_le C n hC hvan
  have := isIso_comparison_app_of_free Dq P n fun i => (hP i).2
  have := isLeftAdjoint_extendScalars.{u, v, u} (Ideal.Quotient.mk I)
  let F := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let FP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  -- `C ⊗ᴸ_R R/I` is computed by the degreewise reduction `FP` of `P`.
  let e : DerivedCategory.Q.obj FP ≅ Dq.functor.obj C :=
    (asIso (Dq.comparison.app P)).symm ≪≫ Dq.functor.mapIso (asIso α)
  have hFP : IsZero (FP.homology n) :=
    ((DerivedCategory.homologyFunctor _ n).map_isZero (hDq.of_iso e)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ n).app FP).symm
  have hP1 : IsZero (P.X (n + 1)) := P.isZero_of_isStrictlyLE n (n + 1) (by omega)
  have hFepi : Epi (F.map (P.d (n - 1) n)) :=
    (isZero_homology_iff_epi_d_of_isZero FP n (F.map_isZero hP1)).1 hFP
  have := (hP n).1
  have hepi : Epi (P.d (n - 1) n) := epi_of_epi_extendScalars_quotient_map hI _ hFepi
  have hPn : IsZero (P.homology n) := (isZero_homology_iff_epi_d_of_isZero P n hP1).2 hepi
  exact (hPn.of_iso ((DerivedCategory.homologyFunctorFactors _ n).app P)).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso (asIso α)).symm

/-- **Derived Nakayama lemma.** Let `I` lie in the Jacobson radical of `R`. A pseudo-coherent
object `C` of `D(R)` whose derived reduction `C ⊗ᴸ_R R/I` vanishes is zero: otherwise its
highest nonzero cohomology `Hⁿ(C)` would be a finite module with `Hⁿ(C) ⊗_R R/I = 0`. -/
theorem isZero_of_isZero_derivedExtensionScalars_quotient
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    {C : DerivedCategory (ModuleCat.{max v u} R)} (hC : IsPseudoCoherent C)
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
        exact isZero_homology_of_isZero_derivedExtensionScalars_quotient hI Dq ⟨E, hE, ⟨e⟩⟩
          hDq _ ih
  have hall : ∀ i : ℤ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C) := fun i =>
    hstep (b - i + 1).toNat i (by omega)
  have : IsIso (0 : (0 : DerivedCategory (ModuleCat.{max v u} R)) ⟶ C) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    exact ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _)).isIso (hall i) _
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategory (ModuleCat.{max v u} R)) ⟶ C)).symm

/-- **Derived reduction modulo an ideal in the Jacobson radical detects isomorphisms of
pseudo-coherent objects.** Let `I` lie in the Jacobson radical of `R` and let `f : K ⟶ L` be a
morphism of pseudo-coherent objects of `D(R)`. If `f ⊗ᴸ_R R/I` is an isomorphism, then so is
`f`: its cone is pseudo-coherent and has vanishing derived reduction modulo `I`. -/
theorem isIso_of_isIso_derivedExtensionScalars_quotient_map
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    {K L : DerivedCategory (ModuleCat.{max v u} R)} (hK : IsPseudoCoherent K)
    (hL : IsPseudoCoherent L) (f : K ⟶ L) (hf : IsIso (Dq.functor.map f)) :
    IsIso f := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle f
  have hC : IsPseudoCoherent C :=
    isPseudoCoherent_obj₃_of_distinguished (Triangle.mk f g h) hT hK hL
  have hDC : IsZero (Dq.functor.obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ (Dq.functor.map_distinguished _ hT)).2 hf
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_derivedExtensionScalars_quotient hI Dq hC hDC)

/-- If `R` is complete with respect to an ideal `J`, every nonzero power of `J` lies in the
Jacobson radical of `R`. -/
theorem pow_le_jacobson_bot_of_isAdicComplete {R : Type u} [CommRing R] {J : Ideal R}
    [IsAdicComplete J R] {N : ℕ} (hN : N ≠ 0) :
    J ^ N ≤ Ideal.jacobson ⊥ :=
  (Ideal.pow_le_self hN).trans (IsAdicComplete.le_jacobson_bot J)

/-- If `R` is `p`-adically complete, the ideal generated by any nonzero power `p ^ N` lies in
the Jacobson radical of `R`. -/
theorem span_singleton_pow_le_jacobson_bot_of_isAdicComplete {R : Type u} [CommRing R] {p : R}
    [IsAdicComplete (Ideal.span {p}) R] {N : ℕ} (hN : N ≠ 0) :
    Ideal.span {p ^ N} ≤ Ideal.jacobson ⊥ := by
  rw [← Ideal.span_singleton_pow]
  exact pow_le_jacobson_bot_of_isAdicComplete hN

end StacksDraft.PseudoCoherence
