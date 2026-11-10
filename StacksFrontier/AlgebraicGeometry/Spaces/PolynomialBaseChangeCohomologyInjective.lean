module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSpectrumGlobalSectionsRing
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeCanonicalIsIso
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Cohomology of the base change to the affine line over an affine base

Let `T` be an affine object of the site, `A = Γ(T₀, ⊤)`, `f : X ⟶ h_T` quasi-compact and
quasi-separated, `X' = X ×_{h_T} h_{Spec A[t]}` with projection `π' : X' ⟶ X`, and `𝓕` a
quasi-coherent `𝒪_X`-module.  By Stacks 073K, part (2), `H^i(X', π'^*𝓕) = H^i(X, 𝓕) ⊗_A A[t]`:
in particular the map

`⨁ₖ H^i(X, 𝓕) ⟶ H^i(X', π'^*𝓕)`, `(yₖ) ↦ ∑ₖ tᵏ · π'^*(yₖ)`

is injective.

## Main definitions

* `AlgebraicGeometry.Space.polynomialBaseChangeDiagram`: the cartesian square of Stacks 073J.
* `AlgebraicGeometry.Space.polynomialSpectrumGlobalSectionsBasis`: the basis `tᵏ` of
  `Γ(h_{Spec A[t]}, 𝒪)` over `Γ(h_T, 𝒪)`.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_sum_smul_affineCohomologyPullbackOverBase`: if
  `∑ₖ tᵏ · π'^*(yₖ) = 0` in `H^i(X', π'^*𝓕)` then all `yₖ = 0`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.eq_zero_of_sum_smul_cohomologyPullbackMap`: the same
  for a basis `(bₖ)` of `Γ(Y', 𝒪)` over `Γ(Y, 𝒪)` in a general square of Stacks 073J.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open Stacks.SheafOfModules.Tensor (ringSheaf)
open ChangeOfRings
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

universe v w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- **The cartesian square of Stacks 073J for the base change to the affine line**, with the
coefficient `𝓕`. -/
abbrev polynomialBaseChangeDiagram (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) : BaseChangeDiagram B S hS where
  X' := algebraBaseChange B S hS T f (Polynomial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  X := X
  Y' := schemeSpace
    (algebraSpectrumOver B S hS T (Polynomial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))
  Y := schemeSpace T
  g' := algebraBaseChangeProjection B S hS T f _
  f' := algebraBaseChangeStructure B S hS T f _
  f := f
  g := schemeSpaceMap (algebraSpectrumSiteHom B S hS T _)
  isPullback := IsPullback.of_hasPullback _ _
  F := F
  isQuasicoherent := hF

/-- `h_{Spec A[t]} ⟶ h_T` is flat. -/
theorem isFlat_polynomialSpectrumSiteHom :
    IsFlat B S hS (schemeSpaceMap (algebraSpectrumSiteHom B S hS T
      (Polynomial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))).hom := by
  refine isFlat_yoneda_map B S hS _ ?_
  change Flat (algebraSpectrumMap B S hS T _)
  unfold algebraSpectrumMap
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      (Polynomial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  infer_instance

/-- `A[t]` for `A = Γ(T₀, ⊤)`. -/
abbrev basePolynomialRing : Type u := Polynomial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)

/-- `Γ(h_T, 𝒪)`. -/
abbrev affineObjectGlobalSections :=
  RingCat.sectionsSubring
    (ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O).obj

/-- `Γ(h_{Spec A[t]}, 𝒪)`. -/
abbrev polynomialSpectrumGlobalSections :=
  RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
    (schemeSpace (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T))).1
    (schemeSpace (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T))).2).O).obj

/-- `Γ(h_{Spec A[t]}, 𝒪)` as a module over `Γ(h_T, 𝒪)`. -/
abbrev polynomialSpectrumGlobalSectionsModule :
    ModuleCat.{u + 1} (affineObjectGlobalSections B S hS T) :=
  (ModuleCat.restrictScalars.{u + 1} (globalSectionsRingHomSite B S hS
    (schemeSpaceMap (algebraSpectrumSiteHom B S hS T (basePolynomialRing B S hS T))))).obj
    (ModuleCat.of _ (polynomialSpectrumGlobalSections B S hS T))

/-- **A basis `(tᵏ)` transported from `A[t]`.**  If `S₀ ≅ A[t]` and `R₀ ≅ A` as rings, compatibly
with a ring map `g : R₀ ⟶ S₀`, then an `R₀`-module `M` additively equivalent to `S₀`, with scalars
acting through `g`, has the basis corresponding to the monomials `tᵏ`. -/
def Module.Basis.ofPolynomialRingEquiv {R₀ S₀ A : Type*} [CommRing R₀] [CommRing S₀] [CommRing A]
    (g : R₀ →+* S₀) (eT : R₀ ≃+* A) (eP : S₀ ≃+* Polynomial A)
    (h : ∀ c, eP (g c) = Polynomial.C (eT c)) {M : Type*} [AddCommGroup M] [Module R₀ M]
    (e : M ≃+ S₀) (he : ∀ c m, e (c • m) = g c * e m) : Module.Basis ℕ R₀ M :=
  Module.Basis.ofRepr <| AddEquiv.toLinearEquiv
    (((e.trans eP.toAddEquiv).trans (Polynomial.basisMonomials A).repr.toAddEquiv).trans
      (Finsupp.mapRange.addEquiv eT.symm.toAddEquiv))
    (fun c m => by
      change Finsupp.mapRange eT.symm (map_zero _)
          ((Polynomial.basisMonomials A).repr (eP (e (c • m)))) =
        c • Finsupp.mapRange eT.symm (map_zero _) ((Polynomial.basisMonomials A).repr (eP (e m)))
      rw [he, map_mul, h, ← Polynomial.smul_eq_C_mul, map_smul]
      ext n
      simp)

/-- Under `e`, the `k`-th vector of `Module.Basis.ofPolynomialRingEquiv` is the element of `S₀`
corresponding to `tᵏ`. -/
theorem Module.Basis.ofPolynomialRingEquiv_apply {R₀ S₀ A : Type*} [CommRing R₀] [CommRing S₀]
    [CommRing A] (g : R₀ →+* S₀) (eT : R₀ ≃+* A) (eP : S₀ ≃+* Polynomial A)
    (h : ∀ c, eP (g c) = Polynomial.C (eT c)) {M : Type*} [AddCommGroup M] [Module R₀ M]
    (e : M ≃+ S₀) (he : ∀ c m, e (c • m) = g c * e m) (k : ℕ) :
    e (Module.Basis.ofPolynomialRingEquiv g eT eP h e he k) = eP.symm (Polynomial.X ^ k) := by
  rw [← (e.trans eP.toAddEquiv).symm_apply_apply
    (Module.Basis.ofPolynomialRingEquiv g eT eP h e he k)]
  simp [Module.Basis.ofPolynomialRingEquiv, Polynomial.X_pow_eq_monomial]

/-- `Module.Basis.ofPolynomialRingEquiv` for a ring read as a module by restriction of scalars. -/
def Module.Basis.restrictScalarsSelfOfPolynomialRingEquiv {R₀ S₀ : Type v} {A : Type w}
    [CommRing R₀] [CommRing S₀] [CommRing A] (g : R₀ →+* S₀) (eT : R₀ ≃+* A)
    (eP : S₀ ≃+* Polynomial A) (h : ∀ c, eP (g c) = Polynomial.C (eT c)) :
    Module.Basis ℕ R₀ ((ModuleCat.restrictScalars g).obj (ModuleCat.of S₀ S₀)) :=
  Module.Basis.ofPolynomialRingEquiv (M := (ModuleCat.restrictScalars g).obj (ModuleCat.of S₀ S₀))
    g eT eP h (AddEquiv.refl _) (fun _ _ => rfl)

/-- The `k`-th vector of `Module.Basis.restrictScalarsSelfOfPolynomialRingEquiv` is the element
of `S₀` corresponding to `tᵏ`. -/
theorem Module.Basis.restrictScalarsSelfOfPolynomialRingEquiv_apply {R₀ S₀ : Type v} {A : Type w}
    [CommRing R₀] [CommRing S₀] [CommRing A] (g : R₀ →+* S₀) (eT : R₀ ≃+* A)
    (eP : S₀ ≃+* Polynomial A) (h : ∀ c, eP (g c) = Polynomial.C (eT c)) (k : ℕ) :
    (Module.Basis.restrictScalarsSelfOfPolynomialRingEquiv g eT eP h k : S₀) =
      eP.symm (Polynomial.X ^ k) :=
  Module.Basis.ofPolynomialRingEquiv_apply
    (M := (ModuleCat.restrictScalars g).obj (ModuleCat.of S₀ S₀))
    g eT eP h (AddEquiv.refl _) (fun _ _ => rfl) k

/-- Under `Γ(h_{Spec A[t]}, 𝒪) ≃ A[t]` and `Γ(h_T, 𝒪) ≃ A`, the pullback of global sections along
`h_{Spec A[t]} ⟶ h_T` is the constant-polynomial map `A → A[t]`. -/
theorem algebraSpectrumGlobalSectionsEquiv_polynomial_siteHom
    (c : affineObjectGlobalSections B S hS T) :
    algebraSpectrumGlobalSectionsEquiv B S hS T (basePolynomialRing B S hS T)
        (globalSectionsRingHomSite B S hS
          (schemeSpaceMap (algebraSpectrumSiteHom B S hS T (basePolynomialRing B S hS T))) c) =
      Polynomial.C (schemeSpaceGlobalSectionsEquiv B S hS T c) :=
  algebraSpectrumGlobalSectionsEquiv_siteHom B S hS T (basePolynomialRing B S hS T) c

/-- **The basis `(tᵏ)` of `Γ(h_{Spec A[t]}, 𝒪)` over `Γ(h_T, 𝒪)`.** -/
def polynomialSpectrumGlobalSectionsBasis :
    Module.Basis ℕ (affineObjectGlobalSections B S hS T)
      (polynomialSpectrumGlobalSectionsModule B S hS T) :=
  Module.Basis.restrictScalarsSelfOfPolynomialRingEquiv
    (globalSectionsRingHomSite B S hS
      (schemeSpaceMap (algebraSpectrumSiteHom B S hS T (basePolynomialRing B S hS T))))
    (schemeSpaceGlobalSectionsEquiv B S hS T)
    (algebraSpectrumGlobalSectionsEquiv B S hS T (basePolynomialRing B S hS T))
    (algebraSpectrumGlobalSectionsEquiv_polynomial_siteHom B S hS T)

/-- The `k`-th vector of `polynomialSpectrumGlobalSectionsBasis` is the global section
corresponding to `tᵏ ∈ A[t]`. -/
theorem polynomialSpectrumGlobalSectionsBasis_apply (k : ℕ) :
    (polynomialSpectrumGlobalSectionsBasis B S hS T k : polynomialSpectrumGlobalSections B S hS T) =
      (algebraSpectrumGlobalSectionsEquiv B S hS T (basePolynomialRing B S hS T)).symm
        (Polynomial.X ^ k) :=
  Module.Basis.restrictScalarsSelfOfPolynomialRingEquiv_apply
    (globalSectionsRingHomSite B S hS
      (schemeSpaceMap (algebraSpectrumSiteHom B S hS T (basePolynomialRing B S hS T))))
    (schemeSpaceGlobalSectionsEquiv B S hS T)
    (algebraSpectrumGlobalSectionsEquiv B S hS T (basePolynomialRing B S hS T))
    (algebraSpectrumGlobalSectionsEquiv_polynomial_siteHom B S hS T) k

/-- An injective map out of an extension of scalars `S₀ ⊗_{R₀} H` along a ring map with a basis
`(bₖ)` of `S₀` over `R₀` separates the families `(yₖ)`: if `∑ₖ Ψ(bₖ ⊗ yₖ) = 0` then `y = 0`. -/
theorem ModuleCat.eq_zero_of_sum_extendScalars_tmul {R₀ S₀ : Type v} [CommRing R₀] [CommRing S₀]
    (g : R₀ →+* S₀) {H : ModuleCat.{v} R₀} {M : ModuleCat.{v} S₀}
    (Ψ : (ModuleCat.extendScalars g).obj H ⟶ M) (hΨ : Function.Injective Ψ.hom)
    (b : Module.Basis ℕ R₀ ((ModuleCat.restrictScalars g).obj (ModuleCat.of S₀ S₀)))
    (v : ℕ →₀ H) (hv : (v.sum fun k y => Ψ.hom (b k ⊗ₜ[R₀,g] y)) = 0) : v = 0 := by
  refine (TensorProduct.equivFinsuppOfBasisLeft b).symm.injective ?_
  rw [map_zero]
  refine hΨ ((?_ : Ψ.hom ((TensorProduct.equivFinsuppOfBasisLeft b).symm v) = 0).trans
    (map_zero Ψ.hom).symm)
  rw [← hv, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
  exact map_finsuppSum Ψ.hom v
    (fun i n => (show ↥((ModuleCat.extendScalars g).obj H) from b i ⊗ₜ[R₀] n))

/-- **Stacks 073K, part (2), for the affine line: the monomials are independent in cohomology.**
If `∑ₖ tᵏ · π'^*(yₖ) = 0` in `H^i(X', π'^*𝓕)` then all `yₖ = 0`. -/
theorem eq_zero_of_sum_smul_affineCohomologyPullbackOverBase (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom) (i : ℕ)
    (hY : IsAffineSpace B S hS (schemeSpace T).1)
    (hY' : IsAffineSpace B S hS
      (schemeSpace (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T))).1)
    (v : ℕ →₀ ((polynomialBaseChangeDiagram B S hS T f F hF).affineCohomologyOverBase i))
    (hv : (v.sum fun k y => (show polynomialSpectrumGlobalSections B S hS T from
        polynomialSpectrumGlobalSectionsBasis B S hS T k) •
      (show ↥((polynomialBaseChangeDiagram B S hS T f F hF).affineCohomologyTarget i) from
      ((polynomialBaseChangeDiagram B S hS T f F hF).affineCohomologyPullbackOverBase
        (isFlat_polynomialSpectrumSiteHom B S hS T) hY hY' i).hom y)) = 0) :
    v = 0 := by
  have hiso := @BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap _ _ _
    (polynomialBaseChangeDiagram B S hS T f F hF)
    (idEtaleChart B S hS T) (IsIso.id (yoneda.obj T))
    (idEtaleChart B S hS (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T)))
    (IsIso.id (yoneda.obj (algebraSpectrumOver B S hS T (basePolynomialRing B S hS T)))) hZ
    (isFlat_polynomialSpectrumSiteHom B S hS T) hqc hqs
    (inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T)))
    (inferInstanceAs (IsAffine (Spec (.of (basePolynomialRing B S hS T))))) i
  exact ModuleCat.eq_zero_of_sum_extendScalars_tmul _
    ((polynomialBaseChangeDiagram B S hS T f F hF).affineCohomologyBaseChangeMap
      (isFlat_polynomialSpectrumSiteHom B S hS T) hY hY' i)
    ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1
    (polynomialSpectrumGlobalSectionsBasis B S hS T) v hv

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
attribute [local instance 5000] SheafOfModules.instAbelian in
/-- The pullback map of Stacks 073K read over the base is the pullback map on elements. -/
theorem BaseChangeDiagram.affineCohomologyPullbackOverBase_hom_apply_eq
    (D : BaseChangeDiagram B S hS) (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      D.affineCohomologyOverBase i) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologyPullbackOverBase hg hY hY' i).hom h =
      (cohomologyPullbackMap B S hS D.g' (D.isAffineHom_g' hY hY') (D.isFlat_g' hg) D.F
        D.isQuasicoherent i).hom h :=
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
attribute [local instance 5000] SheafOfModules.instAbelian in
/-- **Stacks 073K, part (2): a basis of `Γ(Y')` over `Γ(Y)` stays independent in cohomology.**
For a basis `(bₖ)` of `B = Γ(Y', 𝒪)` over `A = Γ(Y, 𝒪)`, if `∑ₖ bₖ · g'^*(yₖ) = 0` in
`H^i(X', 𝓕')` (with `bₖ` read on `X'` through `f'`) then all `yₖ = 0`. -/
theorem BaseChangeDiagram.eq_zero_of_sum_smul_cohomologyPullbackMap (D : BaseChangeDiagram B S hS)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] (V₀' : SmallEtale B S hS D.Y'.1)
    [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hg : IsFlat B S hS D.g.hom)
    (hqc : IsQuasiCompact B S hS D.f.hom) (hqs : IsQuasiSeparated B S hS D.f.hom) (i : ℕ)
    (b : Module.Basis ℕ (RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj)
      ((ModuleCat.restrictScalars.{u + 1} (globalSectionsRingHomSite B S hS D.g)).obj
        (ModuleCat.of _ (RingCat.sectionsSubring
          (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj))))
    (v : ℕ →₀ (D.affineCohomologyOverBase i)) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    (v.sum fun k y => globalSectionsRingHomSite B S hS D.f'
        (show RingCat.sectionsSubring
          (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj from b k) •
      (show ↥(((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived i).obj
            D.pulledBack) from
        (cohomologyPullbackMap B S hS D.g'
          (D.isAffineHom_g' (isAffineSpace_of_isIso_chart B S hS D.Y V₀)
            (isAffineSpace_of_isIso_chart B S hS D.Y' V₀')) (D.isFlat_g' hg) D.F
          D.isQuasicoherent i).hom y)) = 0 → v = 0 := fun hv => by
  have hiso := D.isIso_affineCohomologyBaseChangeMap V₀ V₀' hZ hg hqc hqs i
  exact ModuleCat.eq_zero_of_sum_extendScalars_tmul _
    (D.affineCohomologyBaseChangeMap hg (isAffineSpace_of_isIso_chart B S hS D.Y V₀)
      (isAffineSpace_of_isIso_chart B S hS D.Y' V₀') i)
    ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1 b v hv

end AlgebraicGeometry.Space

end
