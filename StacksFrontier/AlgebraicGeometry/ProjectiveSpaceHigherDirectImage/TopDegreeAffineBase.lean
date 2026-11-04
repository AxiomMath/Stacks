module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeVanishing
public import StacksFrontier.RingTheory.MvPolynomial.HomogeneousBasis

/-!
# The top higher direct image of a twist over an affine base

Let `W` be an affine scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_W ⟶ W`
be the structure morphism. The degree-`n` row of the display of [Stacks, Tag 01XW] reads

`Rⁿ f_* 𝒪(d) = Hom_{𝒪_W}((𝒪_W[T₀, …, Tₙ])_{-n-1-d}, 𝒪_W)`,

and the degree-`e` part of a polynomial algebra is free on the monomials of total degree `e`, so
over an affine base the right-hand side is the free `𝒪_W`-module on the degree-`(-n-1-d)`
monomials. That identification is what this file proves.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.projCompare`: the comparison of
  `Proj Γ(W, ⊤)[T₀, …, Tₙ]` with `ℙⁿ_W` for an affine `W`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
  `.rightDerivedPlusPushforwardTwistOverTopIso`: **`Rⁿ f_* 𝒪(d)` is the free `𝒪_W`-module on the
  degree-`(-n-1-d)` monomials**, for an affine base `W`, for `n = m + 1 ≥ 1` and for every
  integer `d`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.coeffScalar_eq_comp_appTop`: the
  coefficient scalars of Serre's computation over `Γ(W, ⊤)` are the global sections of the
  comparison composed with those of the structure morphism of `ℙⁿ_W`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isQuasicoherent_free`: a free sheaf
  of modules on a scheme is quasi-coherent.

## Implementation notes

**The route.** Over an affine base a quasi-coherent module is determined by its global sections,
`Stacks.AlgebraicGeometry.ModuleLimits.isoOfGlobalSectionsIso`, so the statement is reduced to an
isomorphism of `Γ(W, ⊤)`-modules. Four identifications produce it: [Stacks, Tag 01XK] reads the
global sections of `Rⁿ f_* 𝒪(d)` as `Hⁿ(ℙⁿ_W, 𝒪(d))`; the comparison `projCompare` of the two
models of projective space over `Γ(W, ⊤)` carries that cohomology to Serre's
`Stacks.ProjectiveSpace.Cohomology.twistCohomology`, the scalars being matched by
`coeffScalar_eq_comp_appTop`; [Stacks, Tag 01XU] computes the latter as the dual of a space of
homogeneous polynomials; and the monomial basis of that space dualises to a basis indexed by the
degree-`(-n-1-d)` monomials.

**The two cases.** For `-n - 1 < d` the index type is empty and both sides are zero objects, the
left-hand one by
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt`; only the range `d ≤ -n - 1`, where
the monomials exist, goes through the global-sections comparison.

**The derived category.** `HasDerivedCategory.standard` is installed at priority `2000`, as in
the two modules whose statements are composed here, so that
`CategoryTheory.Functor.rightDerivedPlus` elaborates in the same model as
`isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt`; at the default priority the globally
declared locally small model is preferred and the composition fails on a universe constraint.

**The isomorphism is not canonical.** Both
`Stacks.AlgebraicGeometry.ModuleLimits.isoOfGlobalSectionsIso` and the transport of the twisting
sheaves along the comparison of models are produced through a choice, so what is proved is the
existence of an isomorphism and nothing about its action on sections.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.ProjectiveSpace.Cohomology (coeffScalar twistCohomology serreTwistCohomology)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-! ### The degree-`e` monomials and the dual of the degree-`e` polynomials -/

/-- **The degree-`e` multidegrees are the degree-`k` multidegrees in unlifted variables**, for a
natural number `k` whose image in `ℤ` is `e`: relabelling the variables along `Equiv.ulift` does
not change the total degree. -/
def MonomialIndex.finEquiv (n k : ℕ) {e : ℤ} (hk : (k : ℤ) = e) :
    MonomialIndex.{u} n e ≃ {x : Fin (n + 1) →₀ ℕ | x.degree = k} :=
  Equiv.subtypeEquiv (Finsupp.equivCongrLeft Equiv.ulift) fun x => by
    rw [Finsupp.equivCongrLeft_apply]
    change ((x.degree : ℤ) = e) ↔ ((Finsupp.equivMapDomain Equiv.ulift x).degree = k)
    rw [degree_equivMapDomain_ulift]
    omega

/-- **The `A`-dual of the degree-`k` homogeneous polynomials in `n + 1` variables is free on the
degree-`e` monomials**, for a natural number `k` whose image in `ℤ` is `e`. The monomial basis of
the degree-`k` part is finite, so it has a dual basis. -/
def dualHomogeneousIsoFinsupp (A : Type u) [CommRing A] (n k : ℕ) {e : ℤ} (hk : (k : ℤ) = e) :
    ModuleCat.of A (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A k →ₗ[A] A) ≅
      ModuleCat.of A (MonomialIndex.{u} n e →₀ A) :=
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = k} :=
    (Finsupp.finite_of_degree_eq k).to_subtype
  (((MvPolynomial.basisHomogeneousSubmodule (Fin (n + 1)) A k).dualBasis.repr).trans
    (Finsupp.domLCongr (MonomialIndex.finEquiv.{u} n k hk).symm)).toModuleIso

/-! ### Free sheaves of modules -/

/-- **A free sheaf of modules has a presentation**, with its index type as generators and no
relations: it is the cokernel of the zero morphism out of the free sheaf on the empty type. -/
def freePresentation (X : Scheme.{u}) (I : Type u) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree (ι := PEmpty.{u + 1}) 0 (𝟙 _) (by simp)
    (Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun _ => by simp)
      (fun _ m hm => by simpa using hm))

/-- **A free sheaf of modules on a scheme is quasi-coherent**: it has a global presentation. -/
instance isQuasicoherent_free (X : Scheme.{u}) (I : Type u) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).IsQuasicoherent :=
  (freePresentation X I).isQuasicoherent

/-- **The global sections of a free sheaf of modules on a scheme with a finite index type are the
finitely supported families of global functions.** -/
def freeGlobalSectionsIso (X : Scheme.{u}) (I : Type u) [Finite I] :
    (moduleGlobalSections X).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ModuleCat.of ↥(Γ(X, ⊤)) (I →₀ ↥(Γ(X, ⊤))) :=
  letI := Fintype.ofFinite I
  letI := Classical.decEq I
  (Stacks.SheafOfModules.freeSectionsIso (R := X.ringCatSheaf) I (op (⊤ : X.Opens))).symm ≪≫
    (Finsupp.linearEquivFunOnFinite ↥(Γ(X, ⊤)) ↥(Γ(X, ⊤)) I).symm.toModuleIso

/-! ### The comparison of the two models over an affine base -/

/-- **The comparison of the two models of projective `n`-space over an affine base `W`**: the
`Proj` model over the ring `Γ(W, ⊤)` of global functions, compared with `ℙⁿ_W` through
`Stacks.ProjectiveCohomology.projModelIso` and the base change along `W ≅ Spec Γ(W, ⊤)`. -/
def projCompare (n : ℕ) (W : Scheme.{u}) [IsAffine W] :
    AlgebraicGeometry.Proj (Stacks.ProjectiveCohomology.polyGrading ↥(Γ(W, ⊤)) n) ⟶
      projectiveSpaceOver n W :=
  (Stacks.ProjectiveCohomology.projModelIso ↥(Γ(W, ⊤)) n).hom ≫
    projectiveSpaceOverMap n W.isoSpec.inv

/-- The comparison `projCompare n W` is an isomorphism. -/
instance isIso_projCompare (n : ℕ) (W : Scheme.{u}) [IsAffine W] : IsIso (projCompare n W) :=
  inferInstanceAs (IsIso ((Stacks.ProjectiveCohomology.projModelIso ↥(Γ(W, ⊤)) n).hom ≫
    projectiveSpaceOverMap n W.isoSpec.inv))

/-- **The comparison lies over the base**: composed with the structure morphism of `ℙⁿ_W` it is
the structure morphism of the `Proj` model followed by the identification of `Spec Γ(W, ⊤)`
with `W`. -/
theorem projCompare_comp_structureMorphism (n : ℕ) (W : Scheme.{u}) [IsAffine W] :
    projCompare n W ≫ (projectiveSpaceOver n W ↘ W) =
      Stacks.ProjectiveCohomology.projModelToSpec ↥(Γ(W, ⊤)) n ≫ W.isoSpec.inv := by
  have h1 : projectiveSpaceOverMap n W.isoSpec.inv ≫ (projectiveSpaceOver n W ↘ W) =
      (projectiveSpaceOver n (Spec Γ(W, ⊤)) ↘ Spec Γ(W, ⊤)) ≫ W.isoSpec.inv :=
    projectiveSpaceOverMap_fst n W.isoSpec.inv
  have h2 : (Stacks.ProjectiveCohomology.projModelIso ↥(Γ(W, ⊤)) n).hom ≫
      (projectiveSpaceOver n (Spec Γ(W, ⊤)) ↘ Spec Γ(W, ⊤)) =
      Stacks.ProjectiveCohomology.projModelToSpec ↥(Γ(W, ⊤)) n :=
    Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism ↥(Γ(W, ⊤)) n
  rw [projCompare, Category.assoc, h1, ← Category.assoc, h2]

/-- **The two structure morphisms of `Proj R[T₀, …, Tₙ]` agree.** Both send `r` to the
degree-zero component of `C r`, which is `C r` itself because `C r` is homogeneous of degree
zero. -/
theorem projToSpecCoeff_eq_projModelToSpec (R : Type u) [CommRing R] (n : ℕ) :
    Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n =
      Stacks.ProjectiveCohomology.projModelToSpec R n := by
  refine congrArg (fun φ => AlgebraicGeometry.Proj.toSpecZero
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫ Spec.map φ) ?_
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  show ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.C r)) 0 : MvPolynomial (Fin (n + 1)) R) = MvPolynomial.C r
  exact DirectSum.decompose_of_mem_same _
    ((MvPolynomial.mem_homogeneousSubmodule 0 _).2 (MvPolynomial.isHomogeneous_C _ r))

/-- The identification of `Γ(W, ⊤)` with the global functions of `Spec Γ(W, ⊤)` is the map on
global sections of the inverse of `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem isoSpec_inv_appTop (W : Scheme.{u}) [IsAffine W] :
    W.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(W, ⊤)).inv := by
  refine (Iso.comp_hom_eq_id (Scheme.ΓSpecIso Γ(W, ⊤))).1 ?_
  rw [show (Scheme.ΓSpecIso Γ(W, ⊤)).hom = W.isoSpec.hom.appTop from
    (Scheme.toSpecΓ_appTop W).symm, ← Scheme.Hom.comp_appTop, W.isoSpec.hom_inv_id]
  rfl

/-- **The coefficient scalars of Serre's computation are the scalars of the structure morphism of
`ℙⁿ_W`, read through the comparison of models.** -/
theorem coeffScalar_eq_comp_appTop (n : ℕ) (W : Scheme.{u}) [IsAffine W] :
    coeffScalar ↥(Γ(W, ⊤)) n =
      RingHom.comp ((projCompare n W).appTop).hom
        ((projectiveSpaceOver n W ↘ W).appTop).hom := by
  have h := congrArg (fun φ : AlgebraicGeometry.Proj
      (Stacks.ProjectiveCohomology.polyGrading ↥(Γ(W, ⊤)) n) ⟶ W => φ.appTop)
    (projCompare_comp_structureMorphism n W)
  simp only [Scheme.Hom.comp_appTop] at h
  rw [isoSpec_inv_appTop W] at h
  refine Eq.trans ?_ (congrArg CommRingCat.Hom.hom h.symm)
  rw [← Stacks.ProjectiveSpace.Cohomology.ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar
    ↥(Γ(W, ⊤)) n, projToSpecCoeff_eq_projModelToSpec]
  rfl

/-! ### Transporting Serre's computation to `ℙⁿ_W` -/

/-- **The direct image of the `Proj` model's `𝒪(d)` along the comparison is `𝒪(d)` on
`ℙⁿ_W`.** -/
theorem nonempty_pushforward_twistingSheaf_iso (n : ℕ) (W : Scheme.{u}) [IsAffine W] (d : ℤ) :
    Nonempty ((Scheme.Modules.pushforward (projCompare n W)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.ProjectiveCohomology.polyGrading ↥(Γ(W, ⊤)) n) d) ≅ twistOver n W d) := by
  obtain ⟨e⟩ :=
    Stacks.ProjectiveCohomology.nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv
      ↥(Γ(W, ⊤)) n d
      (Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport ↥(Γ(W, ⊤)) n d)
  refine ⟨((Scheme.Modules.pushforwardComp
      (Stacks.ProjectiveCohomology.projModelIso ↥(Γ(W, ⊤)) n).hom
      (projectiveSpaceOverMap n W.isoSpec.inv)).app _).symm ≪≫ ?_⟩
  refine (Scheme.Modules.pushforward (projectiveSpaceOverMap n W.isoSpec.inv)).mapIso
    ((Stacks.Modules.pushforwardIsoPullbackInv
        (Stacks.ProjectiveCohomology.projModelIso ↥(Γ(W, ⊤)) n)).app _ ≪≫
      e.symm ≪≫ (twistOverPullbackIso n W.isoSpec.inv d).symm) ≪≫ ?_
  exact Stacks.Cohomology.SchemeIso.pushforwardPullbackIso
    (asIso (projectiveSpaceOverMap n W.isoSpec.inv)) (twistOver n W d)

/-- **Serre's cohomology module is the cohomology of `𝒪(d)` on `ℙⁿ_W`**, as a module over
`Γ(W, ⊤)` through the structure morphism. -/
def twistCohomologyIsoRestrictScalars (n : ℕ) (W : Scheme.{u}) [IsAffine W] (d : ℤ) (q : ℕ) :
    twistCohomology ↥(Γ(W, ⊤)) n d q ≅
      (ModuleCat.restrictScalars ((projectiveSpaceOver n W ↘ W).appTop).hom).obj
        (((moduleGlobalSections (projectiveSpaceOver n W)).rightDerived q).obj
          (twistOver n W d)) :=
  ModuleCat.restrictScalarsComp'App ((projectiveSpaceOver n W ↘ W).appTop).hom
      ((projCompare n W).appTop).hom (coeffScalar ↥(Γ(W, ⊤)) n)
      (coeffScalar_eq_comp_appTop n W) _ ≪≫
    (ModuleCat.restrictScalars ((projectiveSpaceOver n W ↘ W).appTop).hom).mapIso
      (rightDerivedEvaluationTopPushforwardIso (projCompare n W) _ q ≪≫
        ((moduleGlobalSections (projectiveSpaceOver n W)).rightDerived q).mapIso
          (nonempty_pushforward_twistingSheaf_iso n W d).some)

/-! ### The identification over an affine base -/

/-- **The global sections of `Rⁿ f_* 𝒪(d)` are the degree-`(-n-1-d)` monomial coefficients**, for
an affine base `W`, for `n = m + 1 ≥ 1` and for `d ≤ -n - 1`. -/
def globalSectionsRightDerivedPlusIso (m : ℕ) (W : Scheme.{u}) [IsAffine W] {d : ℤ}
    (hd : d ≤ -((m + 1 : ℕ) : ℤ) - 1) :
    (moduleGlobalSections W).obj
        (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) W ↘ W)).rightDerivedPlus
          ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) W d)) ≅
      ModuleCat.of ↥(Γ(W, ⊤))
        (MonomialIndex.{u} (m + 1) (-((m + 1 : ℕ) : ℤ) - 1 - d) →₀ ↥(Γ(W, ⊤))) :=
  (moduleGlobalSections W).mapIso ((Stacks.DerivedIndexing.rightDerivedIso
      (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) W ↘ W)) (m + 1)).app
      (twistOver (m + 1) W d)).symm ≪≫
    (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso
      (projectiveSpaceOver (m + 1) W ↘ W) (twistOver (m + 1) W d) (m + 1)).symm ≪≫
    (twistCohomologyIsoRestrictScalars (m + 1) W d (m + 1)).symm ≪≫
    (serreTwistCohomology ↥(Γ(W, ⊤)) m d).degreeTopPolynomial hd ≪≫
    dualHomogeneousIsoFinsupp ↥(Γ(W, ⊤)) (m + 1)
      (-d - (((m + 1 : ℕ) : ℤ) + 1)).toNat (by omega)

/-- **`Rⁿ f_* 𝒪(d)` is the free `𝒪_W`-module on the degree-`(-n-1-d)` monomials**, for the
structure morphism `f : ℙⁿ_W ⟶ W` over an affine base `W`, for `n = m + 1 ≥ 1` and for every
integer `d`.

This is the degree-`n` row of [Stacks, Tag 01XW] over an affine base: the sheaf it identifies
`Rⁿ f_* 𝒪(d)` with is the `𝒪_W`-dual of `(𝒪_W[T₀, …, Tₙ])_{-n-1-d}`, and the degree-`e` part of a
polynomial algebra is free of finite rank on the monomials of total degree `e`, so its dual is
free on the same index set. For `-n - 1 < d` the index set is empty and both sides vanish. -/
def rightDerivedPlusPushforwardTwistOverTopIso (m : ℕ) (W : Scheme.{u}) [IsAffine W] (d : ℤ) :
    (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) W ↘ W)).rightDerivedPlus
        ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) W d)) ≅
      SheafOfModules.free (R := W.ringCatSheaf)
        (MonomialIndex.{u} (m + 1) (-((m + 1 : ℕ) : ℤ) - 1 - d)) := by
  by_cases hd : d ≤ -((m + 1 : ℕ) : ℤ) - 1
  · haveI : Finite {x : Fin (m + 1 + 1) →₀ ℕ |
        x.degree = (-d - (((m + 1 : ℕ) : ℤ) + 1)).toNat} :=
      (Finsupp.finite_of_degree_eq _).to_subtype
    haveI : Finite (MonomialIndex.{u} (m + 1) (-((m + 1 : ℕ) : ℤ) - 1 - d)) :=
      Finite.of_equiv _ (MonomialIndex.finEquiv.{u} (m + 1)
        (-d - (((m + 1 : ℕ) : ℤ) + 1)).toNat (e := -((m + 1 : ℕ) : ℤ) - 1 - d) (by omega)).symm
    exact Stacks.AlgebraicGeometry.ModuleLimits.isoOfGlobalSectionsIso
      (globalSectionsRightDerivedPlusIso m W hd ≪≫ (freeGlobalSectionsIso W _).symm)
  · exact (isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m W (by omega)).iso
      (isZero_baseDegreeSheaf_of_neg (m + 1) W (by omega))

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
