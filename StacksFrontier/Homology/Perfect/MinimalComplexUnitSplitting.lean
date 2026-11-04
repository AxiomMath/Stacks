module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctionsLocal
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Perfect.MinimalComplexFreeCohomology
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Cotangent.KoszulRegularQuotient
public import StacksFrontier.Homology.Perfect.StupidFiltration
public import StacksFrontier.Homology.Perfect.Saturation

/-!
# Splitting off a free summand of rank one in degree zero

Let `M` be a bounded complex of finite projective modules over a commutative ring `R` and `𝔭` a
prime of `R` at which the derived fibre `M ⊗^L_R κ(𝔭)` has no cohomology in negative degrees and
one-dimensional cohomology in degree zero. If moreover `H⁰(M ⊗_R R_f)` is free of rank one over
`R_f` for every `f`, then near `𝔭` the complex `M ⊗_R R_f` is `R_f` in degree zero plus a bounded
complex of finite projective modules in degrees `≥ 1`.

## Main definitions

* `StacksDraft.StupidTruncation.isoStupidTruncBiprodSingleOfDEqZero`: a complex in degrees `≥ p`
  whose differential out of degree `p` vanishes is `σ^{≥p+1}K ⊞ (single p).obj Kᵖ`.

## Main results

* `CochainComplex.d_zero_one_eq_zero_of_ker_linearEquiv`: a differential `d⁰` out of a free
  module of rank one, into a free module, with kernel free of rank one, vanishes.
* `StacksDraft.Perfect.exists_notMem_iso_single_biprod_of_fibre`: near such a prime `𝔭`, the
  complex splits off a free module of rank one in degree zero, the complement being a bounded
  complex of finite projective modules in degrees `≥ 1`.
* `StacksDraft.Perfect.finrank_homology_fibreComplex_comp_ringEquiv`: composing a base change with
  a ring isomorphism onto a field turns cohomology free of rank one into one-dimensional
  cohomology.

## References

* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CochainComplex

/-- **A first differential out of a free module of rank one, into a free module, with kernel free
of rank one, vanishes.** -/
theorem d_zero_one_eq_zero_of_ker_linearEquiv {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (e₀ : P.X 0 ≃ₗ[A] A) {ι : Type*}
    (e₁ : P.X 1 ≃ₗ[A] (ι → A)) (k : LinearMap.ker (P.d 0 1).hom ≃ₗ[A] A) :
    P.d 0 1 = 0 := by
  let d := (P.d 0 1).hom
  let z : P.X 0 := (k.symm 1 : LinearMap.ker d)
  have hz : d z = 0 := (k.symm 1).2
  let a : A := e₀ z
  have ha : ∀ c : A, c * a = 0 → c = 0 := by
    intro c hc
    have h2 : k.symm c = 0 := by
      rw [show k.symm c = c • k.symm 1 by rw [← map_smul, smul_eq_mul, mul_one]]
      exact Subtype.ext (e₀.injective (by rwa [map_smul, map_zero, smul_eq_mul]) : c • z = 0)
    simpa using congrArg k h2
  let w : P.X 0 := e₀.symm 1
  have hxw : ∀ x : P.X 0, x = e₀ x • w := fun x ↦
    e₀.injective (by rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one])
  have hdw : d w = 0 := by
    have h : a • d w = 0 := by rwa [← map_smul, ← hxw z]
    apply e₁.injective
    funext i
    have hi := congrFun (congrArg e₁ h) i
    rw [map_smul, map_zero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rw [map_zero, Pi.zero_apply]
    exact ha _ (by rwa [mul_comm])
  ext x
  show d x = 0
  rw [hxw x, map_smul, hdw, smul_zero]

end CochainComplex

namespace StacksDraft.StupidTruncation

open HomologicalComplex ComplexShape

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- When the differential out of degree `p` vanishes, the projection `σ^{≥p}K ⟶ (single p).obj Kᵖ`
has a section: the inclusion of `Kᵖ` in degree `p`. -/
noncomputable def stupidTruncGESingleSection (p : ℤ) (hd : K.d p (p + 1) = 0) :
    (single C (.up ℤ) p).obj (K.X p) ⟶ K.stupidTrunc (embeddingUpIntGE p) :=
  mkHomFromSingle (stupidTruncGEXIso K p p le_rfl).inv (fun k hk ↦ by
    obtain rfl : p + 1 = k := hk
    have : IsIso ((ιStupidTrunc K (embeddingUpIntGE p)).f (p + 1)) := by
      rw [ιStupidTruncGE_f K p (p + 1) (by omega)]
      infer_instance
    rw [← cancel_mono ((ιStupidTrunc K (embeddingUpIntGE p)).f (p + 1)), Category.assoc,
      ← (ιStupidTrunc K (embeddingUpIntGE p)).comm, ιStupidTruncGE_f K p p le_rfl,
      Iso.inv_hom_id_assoc, hd, zero_comp])

/-- The inclusion `stupidTruncGESingleSection K p hd` of `Kᵖ` in degree `p` is a section of the
projection `stupidTruncGEπ K p`. -/
theorem stupidTruncGESingleSection_π (p : ℤ) (hd : K.d p (p + 1) = 0) :
    stupidTruncGESingleSection K p hd ≫ stupidTruncGEπ K p = 𝟙 _ := by
  apply from_single_hom_ext
  rw [comp_f, stupidTruncGESingleSection, mkHomFromSingle_f, stupidTruncGEπ_f, id_f]
  simp

/-- **A brutal truncation splits off its bottom term when the differential out of it
vanishes**: `σ^{≥p}K ≅ σ^{≥p+1}K ⊞ (single p).obj Kᵖ` if `d^p = 0`. -/
noncomputable def stupidTruncGEIsoBiprodOfDEqZero (p : ℤ) (hd : K.d p (p + 1) = 0) :
    K.stupidTrunc (embeddingUpIntGE p) ≅
      K.stupidTrunc (embeddingUpIntGE (p + 1)) ⊞ (single C (.up ℤ) p).obj (K.X p) :=
  (ShortComplex.Splitting.ofExactOfSection _ (stupidTruncGEShortComplex_shortExact K p).exact
    (stupidTruncGESingleSection K p hd) (stupidTruncGESingleSection_π K p hd)
    (stupidTruncGEShortComplex_shortExact K p).mono_f).isoBinaryBiproduct

/-- **A complex in degrees `≥ p` whose differential out of degree `p` vanishes is
`σ^{≥p+1}K ⊞ (single p).obj Kᵖ`.** -/
noncomputable def isoStupidTruncBiprodSingleOfDEqZero (p : ℤ) [K.IsStrictlyGE p]
    (hd : K.d p (p + 1) = 0) :
    K ≅ K.stupidTrunc (embeddingUpIntGE (p + 1)) ⊞ (single C (.up ℤ) p).obj (K.X p) :=
  haveI := StupidFiltration.isIso_ιStupidTruncGE K p
  (asIso (ιStupidTrunc K (embeddingUpIntGE p))).symm ≪≫ stupidTruncGEIsoBiprodOfDEqZero K p hd

end StacksDraft.StupidTruncation

namespace StacksDraft.Perfect

open CochainComplex.DerivedExtensionScalars StacksDraft.StupidTruncation HomologicalComplex
  ComplexShape

/-- Extension of scalars of a finite free module, `R' ⊗_R R^n ≅ R'^n`. -/
noncomputable def extendScalarsULiftFunLinearEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (ψ : R →+* R') (n : ℕ) :
    letI := ψ.toAlgebra
    (ModuleCat.extendScalars.{u, u, u} ψ).obj (ModuleCat.of R (ULift.{u} (Fin n → R))) ≃ₗ[R']
      (Fin n → R') :=
  letI := ψ.toAlgebra
  ((ULift.moduleEquiv (R := R) (M := Fin n → R)).baseChange R R' _ _).trans
    (TensorProduct.piScalarRight R R' R' (Fin n))

/-- **Near a prime where the derived fibre of a perfect complex is `κ(𝔭)` in degree zero and
nothing below, and where `H⁰` is free of rank one over the principal localizations, the complex
splits off `A'` in degree zero, the complement being a bounded complex of finite projective
modules in degrees `≥ 1`.** -/
theorem exists_notMem_iso_single_biprod_of_fibre {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (N : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [N.IsStrictlyGE a]
    [N.IsStrictlyLE b] (hfin : ∀ j, Module.Finite R (N.X j))
    (hproj : ∀ j, Module.Projective R (N.X j))
    (hneg : ∀ j : ℤ, j < 0 →
      IsZero ((FibreCycleLift.fibreComplex (algebraMap R p.ResidueField) N).homology j))
    (hrank : Module.finrank p.ResidueField
      ((FibreCycleLift.fibreComplex (algebraMap R p.ResidueField) N).homology 0) = 1)
    (A' : R → Type u) [∀ f, CommRing (A' f)] (ψ : ∀ f, R →+* A' f)
    (hψ : ∀ f, letI := (ψ f).toAlgebra; IsLocalization.Away f (A' f))
    (hloc : ∀ f, Nonempty ((FibreCycleLift.fibreComplex (ψ f) N).homology 0 ≃ₗ[A' f] A' f)) :
    ∃ f : R, f ∉ p ∧ ∃ (P : CochainComplex (ModuleCat.{u} (A' f)) ℤ) (b' : ℤ),
      P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b' ∧ (∀ j, Module.Finite (A' f) (P.X j)) ∧
      (∀ j, Module.Projective (A' f) (P.X j)) ∧
      letI := HasDerivedCategory.standard (ModuleCat.{u} (A' f))
      Nonempty (DerivedCategory.Q.obj (FibreCycleLift.fibreComplex (ψ f) N) ≅
        (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of (A' f) (A' f)) ⊞
          DerivedCategory.Q.obj P) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let κ := p.ResidueField
  let := HasDerivedCategory.standard (ModuleCat.{u} κ)
  have : ∀ j, Projective (N.X j) := fun j ↦ (IsProjective.iff_projective (N.X j)).mp (hproj j)
  have hK : IsPerfect (DerivedCategory.Q.obj N) :=
    ⟨N, a, b, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩
  have hpc := isPseudoCoherent_of_isPerfect.{u, u} _ hK
  let eH := fun i : ℤ ↦ homologyTotalDerivedExtensionScalarsQIso (algebraMap R κ)
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R κ)) N b i
  have hvan : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R κ)).functor.obj
        (DerivedCategory.Q.obj N))) := fun i hi ↦ (hneg i hi).of_iso (eH i)
  obtain ⟨f, hf, -, P, b', hPge, hPle, hPX, ⟨eP⟩⟩ :=
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below.{u, u} p
      (DerivedCategory.Q.obj N) hpc ⟨a, inferInstance⟩ 0 hvan
  refine ⟨f, hf, ?_⟩
  let Rf := Localization.Away f
  let := HasDerivedCategory.standard (ModuleCat.{u} Rf)
  let := HasDerivedCategory.standard (ModuleCat.{u} (A' f))
  let := (ψ f).toAlgebra
  have := hψ f
  let σ : Rf →+* A' f := (IsLocalization.algEquiv (Submonoid.powers f) Rf (A' f)).toRingHom
  have hσ : σ.comp (algebraMap R Rf) = ψ f :=
    RingHom.ext fun x ↦ (IsLocalization.algEquiv (Submonoid.powers f) Rf (A' f)).commutes x
  have : ∀ i, Projective (P.X i) := fun i ↦
    Projective.of_iso (hPX i).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis Rf _))
  have := hPge
  have := hPle
  let P' := FibreCycleLift.fibreComplex σ P
  have h₁ := (totalDerivedExtensionScalars.{u, u, u} (ψ f)).comparison_isIso_of_projective N b
  have h₂ := (totalDerivedExtensionScalars.{u, u, u}
    σ).comparison_isIso_of_projective P b'
  let eDer : DerivedCategory.Q.obj (FibreCycleLift.fibreComplex (ψ f) N) ≅
      DerivedCategory.Q.obj P' :=
    (@asIso _ _ _ _ ((totalDerivedExtensionScalars.{u, u, u} (ψ f)).comparison.app N) h₁).symm ≪≫
      eqToIso (congrArg (fun φ ↦ (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
        (DerivedCategory.Q.obj N)) hσ.symm) ≪≫
      ((totalDerivedExtensionScalarsComp.{u, u} (algebraMap R Rf)
        σ).app _).symm ≪≫
      (totalDerivedExtensionScalars.{u, u, u} σ).functor.mapIso eP.symm ≪≫
      @asIso _ _ _ _
        ((totalDerivedExtensionScalars.{u, u, u} σ).comparison.app P) h₂
  let r := fun i : ℤ ↦ Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R κ)).functor.obj
      (DerivedCategory.Q.obj N)))
  have hr0 : r 0 = 1 := ((eH 0).toLinearEquiv.finrank_eq).trans hrank
  let e : ∀ i, P'.X i ≃ₗ[A' f] (Fin (r i) → A' f) := fun i ↦
    ((ModuleCat.extendScalars.{u, u, u} σ).mapIso (hPX i).some).toLinearEquiv.trans
      (extendScalarsULiftFunLinearEquiv σ (r i))
  let e₀ : P'.X 0 ≃ₗ[A' f] A' f :=
    (e 0).trans ((LinearEquiv.funCongrLeft (A' f) (A' f) (finCongr hr0.symm)).trans
      (LinearEquiv.funUnique (Fin 1) (A' f) (A' f)))
  have hz : ∀ i, IsZero (P.X i) → IsZero (P'.X i) := fun i ↦
    (ModuleCat.extendScalars.{u, u, u} σ).map_isZero
  have : P'.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff P' 0).2 fun i hi ↦
    hz i (P.isZero_of_isStrictlyGE 0 i hi)
  have : P'.IsStrictlyLE b' := (CochainComplex.isStrictlyLE_iff P' b').2 fun i hi ↦
    hz i (P.isZero_of_isStrictlyLE b' i hi)
  have hdneg : P'.d (-1) 0 = 0 := (P'.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _
  obtain ⟨h0⟩ := hloc f
  let eH0 : (P').homology 0 ≃ₗ[A' f] A' f :=
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (A' f)) 0).app P').symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (A' f)) 0).mapIso eDer.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (A' f)) 0).app
        (FibreCycleLift.fibreComplex (ψ f) N)).toLinearEquiv.trans h0
  have hd0 : P'.d 0 (0 + 1) = 0 :=
    CochainComplex.d_zero_one_eq_zero_of_ker_linearEquiv P' e₀ (e 1)
      ((CochainComplex.kerLinearEquivHomologyZero P' hdneg).trans eH0)
  let T : CochainComplex (ModuleCat.{u} (A' f)) ℤ := P'.stupidTrunc (embeddingUpIntGE (0 + 1))
  have hT1 : T.IsStrictlyGE 1 := inferInstanceAs (T.IsStrictlyGE (0 + 1))
  have hT0 : ∀ i, ¬0 + 1 ≤ i → IsZero (T.X i) := fun i hi ↦
    T.isZero_of_isStrictlyGE (0 + 1) i (by omega)
  have hTX : ∀ i, Module.Finite (A' f) (T.X i) ∧ Module.Projective (A' f) (T.X i) := by
    intro i
    by_cases hi : 0 + 1 ≤ i
    · let eT := (stupidTruncGEXIso P' (0 + 1) i hi).toLinearEquiv.trans (e i)
      exact ⟨Module.Finite.equiv eT.symm, Module.Projective.of_equiv eT.symm⟩
    · have := ModuleCat.subsingleton_of_isZero (hT0 i hi)
      exact ⟨inferInstance, inferInstance⟩
  have hTle : T.IsStrictlyLE b' := (CochainComplex.isStrictlyLE_iff T b').2 fun i hi ↦ by
    by_cases h : 0 + 1 ≤ i
    · exact (P'.isZero_of_isStrictlyLE b' i hi).of_iso (stupidTruncGEXIso P' (0 + 1) i h)
    · exact hT0 i h
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (DerivedCategory.Q (C := ModuleCat.{u} (A' f)))
  refine ⟨T, b', hT1, hTle, fun j ↦ (hTX j).1, fun j ↦ (hTX j).2, ⟨?_⟩⟩
  exact eDer ≪≫ DerivedCategory.Q.mapIso (isoStupidTruncBiprodSingleOfDEqZero P' 0 hd0) ≪≫
    DerivedCategory.Q.mapBiprod _ _ ≪≫
    biprod.mapIso (Iso.refl _)
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (A' f)) 0).app _).symm ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} (A' f)) 0).mapIso e₀.toModuleIso) ≪≫
    biprod.braiding _ _

/-- **The fibre dimension in one degree is unchanged by composing a base change with a ring
isomorphism onto a field.** If `A' ⊗_A F` has degree-`j` cohomology free of rank one, then
`K ⊗_A F` has one-dimensional degree-`j` cohomology for any ring isomorphism `e : A' ≅ K` onto a
field. -/
theorem finrank_homology_fibreComplex_comp_ringEquiv {A A' K : Type u} [CommRing A] [CommRing A']
    [Field K] (φ : A →+* A') (e : A' ≃+* K) (F : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)
    (h : Nonempty ((FibreCycleLift.fibreComplex φ F).homology j ≅ ModuleCat.of A' A')) :
    Module.finrank K ((FibreCycleLift.fibreComplex ((e : A' →+* K).comp φ) F).homology j) = 1 := by
  let G := ModuleCat.extendScalars.{u, u, u} (e : A' →+* K)
  have hflat : (e : A' →+* K).Flat := RingHom.Flat.of_bijective e.bijective
  have : PreservesFiniteLimits G := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  have : G.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj (e : A' →+* K)).isLeftAdjoint
  have : Nontrivial A' := (e : A' →+* K).domain_nontrivial
  let i := (HomologicalComplex.homologyFunctor _ _ j).mapIso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ (e : A' →+* K))
        (ComplexShape.up ℤ)).app F) ≪≫
    ((FibreCycleLift.fibreComplex φ F).sc j).mapHomologyIso G ≪≫ G.mapIso h.some
  let := (e : A' →+* K).toAlgebra
  refine i.toLinearEquiv.finrank_eq.trans ?_
  show Module.finrank K (TensorProduct A' K A') = 1
  rw [Module.finrank_baseChange, Module.finrank_self]

end StacksDraft.Perfect

end
