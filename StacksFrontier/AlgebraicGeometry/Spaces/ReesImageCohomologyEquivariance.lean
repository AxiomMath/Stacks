module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesCohomologyFiltrationStable

/-!
# Equivariance of the comparison of the Rees module with the cohomology of `X_R`

Let `T` be an affine object of the site with Noetherian `A = Γ(T₀, ⊤)`, `f : X ⟶ h_T`,
`J ⊆ A` an ideal, `R = A[Jt] ⊆ A[t]` its Rees algebra, `π : X_R ⟶ X` the base change, and `G`
the image of `π^*N ⟶ ψ_*ψ^*π^*N` (`AlgebraicGeometry.Space.algebraImageModule`).  The map
`Φ : H^p(X_R, G) ≅ H^p(X, π_*G) ⟶ H^p(X, π_*ψ_*ψ^*π^*N)` (Stacks 0D2U followed by the inclusion)
is `R`-equivariant, `R` acting on the target through `A[t]`.  This is the `hΦ` input of
`Ideal.Filtration.stable_of_reesAction` in the proof of [Stacks, Tag 08AX].

## Main results

* `ModuleCat.map_comp_iso_smul_of_comm`, `ModuleCat.map_comp_inv_eq_of_fac`: abstract forms.
* `AlgebraicGeometry.Space.cohomologyPushforwardLinearIso_globalSmul_comm`: Stacks 0D2U carries
  multiplication by a global function to the induced endomorphism, for any `ι : π_*G ⟶ V`.
* `AlgebraicGeometry.Space.reesImageCohomology_smul`: the `R`-equivariance of `Φ`.
* `Ideal.Filtration.stable_of_reesAction_moduleCat`: `Ideal.Filtration.stable_of_reesAction`
  for modules over rings of global functions.

## Implementation notes

The equivariance is proved for an arbitrary `ι` with the scalar compatibility as a hypothesis and
only then instantiated at `AlgebraicGeometry.Space.algebraImageModuleι`: elaborating it directly at
the image inclusion does not finish.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

universe v u

/-- A commuting square `a ≫ b = c ≫ d` read on an element of a module-valued functor. -/
private theorem map_apply_eq_of_comp_eq {C : Type*} [Category C] {Γ : Type*} [Ring Γ]
    (H : C ⥤ ModuleCat.{v} Γ) {X Y Z W : C} {a : X ⟶ Y} {b : Y ⟶ W} {c : X ⟶ Z} {d : Z ⟶ W}
    (h : a ≫ b = c ≫ d) (z : H.obj X) :
    (H.map b).hom ((H.map a).hom z) = (H.map d).hom ((H.map c).hom z) := by
  simpa using ConcreteCategory.congr_hom (congrArg H.map h) z

/-- **A comparison carrying `g` to `P(g)` transports multiplication by `b`.** -/
theorem ModuleCat.map_comp_iso_smul_of_comm {C C' : Type*} [Category C] [Category C'] {Γ Γ' : Type*}
    [CommRing Γ] [CommRing Γ'] (H : C ⥤ ModuleCat.{v} Γ) (H' : C' ⥤ ModuleCat.{v} Γ')
    (φ : Γ →+* Γ') (P : C' ⥤ C) {G : C'} {V : C} (g : G ⟶ G) (ι : P.obj G ⟶ V) (ρ : V ⟶ V)
    (cG : (ModuleCat.restrictScalars φ).obj (H'.obj G) ≅ H.obj (P.obj G))
    (hnat : (ModuleCat.restrictScalars φ).map (H'.map g) ≫ cG.hom = cG.hom ≫ H.map (P.map g))
    (hι : P.map g ≫ ι = ι ≫ ρ) (b : Γ') (hg : H'.map g = b • 𝟙 _) (z : H'.obj G) :
    (H.map ι).hom (cG.hom.hom (b • z)) = (H.map ρ).hom ((H.map ι).hom (cG.hom.hom z)) := by
  have e1 : (b • z) = (H'.map g).hom z := by rw [hg]; rfl
  have e2 : cG.hom.hom ((H'.map g).hom z) = (H.map (P.map g)).hom (cG.hom.hom z) :=
    congrArg (fun m => m.hom z) hnat
  rw [e1, e2]
  exact map_apply_eq_of_comp_eq H hι _

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0D2U carries multiplication by a global function to the induced endomorphism**: for
`ι : π_*G ⟶ V` with `π_*(c ·) ≫ ι = ι ≫ ρ`, `H^p(ι)(c · z) = H^p(ρ)(H^p(ι) z)`. -/
theorem cohomologyPushforwardLinearIso_globalSmul_comm {X X' : AlgebraicSpaces B S hS}
    (π : X' ⟶ X) (hπ : IsAffineHom B S hS π.hom) (G : Modules.{u, u} B S hS X'.1 X'.2)
    (hG : G.IsQuasicoherentOnSite) {V : Modules.{u, u} B S hS X.1 X.2}
    (ι : (modulePushforward B S hS π).obj G ⟶ V) (ρ : V ⟶ V)
    (c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj)
    (hι : (modulePushforward B S hS π).map (globalSmul _ c G) ≫ ι = ι ≫ ρ) (p : ℕ)
    (z : (modulesCohomologyFunctor B S hS X' p).obj G) :
    ((modulesCohomologyFunctor B S hS X p).map ι).hom
        ((cohomologyPushforwardLinearIsoOfIsAffineHom B S hS π hπ G hG p).hom.hom (c • z)) =
      ((modulesCohomologyFunctor B S hS X p).map ρ).hom
        (((modulesCohomologyFunctor B S hS X p).map ι).hom
          ((cohomologyPushforwardLinearIsoOfIsAffineHom B S hS π hπ G hG p).hom.hom z)) := by
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  exact ModuleCat.map_comp_iso_smul_of_comm (modulesCohomologyFunctor B S hS X p)
    (modulesCohomologyFunctor B S hS X' p) (globalSectionsRingHomSite B S hS π)
    (modulePushforward B S hS π) (globalSmul _ c G) ι ρ
    (cohomologyPushforwardLinearIsoOfIsAffineHom B S hS π hπ G hG p)
    (cohomologyPushforwardLinearIsoOfIsAffineHom_hom_naturality B S hS π hπ hG hG _ p)
    hι c (rightDerived_globalSections_map_globalSmul B S hS X' c G p) z


/-- Abstract form of the degree-`k` membership: a factorization `w ≫ ι = incl ≫ u ≫ ρ` read on
cohomology, through an isomorphism `c` onto the cohomology of the source of `ι`. -/
theorem _root_.ModuleCat.map_comp_inv_eq_of_fac {C : Type*} [Category C] {Γ : Type*} [Ring Γ]
    (H : C ⥤ ModuleCat.{v} Γ) {N₁ N V W : C} (incl : N₁ ⟶ N) (u : N ⟶ V) (ρ : V ⟶ V)
    (w : N₁ ⟶ W) (ι : W ⟶ V) (hw : w ≫ ι = incl ≫ u ≫ ρ) {M' : ModuleCat.{v} Γ}
    (c : M' ≅ H.obj W) (z : H.obj N₁) :
    (H.map ι).hom (c.hom.hom (c.inv.hom ((H.map w).hom z))) =
      (H.map ρ).hom ((H.map u).hom ((H.map incl).hom z)) := by
  have e1 : c.hom.hom (c.inv.hom ((H.map w).hom z)) = (H.map w).hom z :=
    congrArg (fun m => m.hom ((H.map w).hom z)) c.inv_hom_id
  rw [e1]
  simpa using map_apply_eq_of_comp_eq H hw z

/-- **`Ideal.Filtration.stable_of_reesAction` for modules over the rings of global functions**:
the filtration lives on `M₀` read over `A` along `g`, the Rees module embeds in `Q`, and the
finite `A[Jt]`-module is `P₀` read along `gR`, mapped to `Q` through `c : P₀ ≅ W` and `ι`. -/
theorem Ideal.Filtration.stable_of_reesAction_moduleCat {A Γ Γ' : Type*} [CommRing A]
    [IsNoetherianRing A] [CommRing Γ] [CommRing Γ'] {J : Ideal A} (g : A →+* Γ)
    (M₀ : ModuleCat.{v} Γ) (hM : Module.Finite A ((ModuleCat.restrictScalars g).obj M₀))
    (F : J.Filtration ((ModuleCat.restrictScalars g).obj M₀)) (Q : ModuleCat.{v} Γ)
    (χ : Polynomial A →+* AddMonoid.End Q) (u : M₀ ⟶ Q)
    (hu : ∀ (a : A) (m : M₀), u.hom (g a • m) = χ (Polynomial.C a) (u.hom m))
    (hinj : ∀ v : ℕ →₀ M₀, (v.sum fun k y => χ (Polynomial.X ^ k) (u.hom y)) = 0 → v = 0)
    (gR : reesAlgebra J →+* Γ') (P₀ : ModuleCat.{v} Γ')
    (hP : Module.Finite (reesAlgebra J) ((ModuleCat.restrictScalars gR).obj P₀))
    (gπ : Γ →+* Γ') (W : ModuleCat.{v} Γ) (c : (ModuleCat.restrictScalars gπ).obj P₀ ≅ W)
    (ι : W ⟶ Q)
    (hΦ : ∀ (r : reesAlgebra J) (z : P₀),
      ι.hom (c.hom.hom (gR r • z)) = χ (r : Polynomial A) (ι.hom (c.hom.hom z)))
    (N₁ : ℕ → ModuleCat.{v} Γ) (incl : ∀ k, N₁ k ⟶ M₀)
    (hN : ∀ k, F.N k = LinearMap.range ((ModuleCat.restrictScalars g).map (incl k)).hom)
    (hsub : ∀ k (z : N₁ k), ∃ q : P₀,
      ι.hom (c.hom.hom q) = χ (Polynomial.X ^ k) (u.hom ((incl k).hom z))) :
    F.Stable := by
  have := hM
  have := hP
  refine Ideal.Filtration.stable_of_reesAction F χ u.hom.toAddMonoidHom
    (fun a m => hu a m) hinj (P := (ModuleCat.restrictScalars gR).obj P₀)
    ((ι.hom.toAddMonoidHom).comp (c.hom.hom.toAddMonoidHom))
    (fun r z => hΦ r z) ?_
  intro k y hy
  rw [hN k] at hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨q, hq⟩ := hsub k z
  exact ⟨q, hq⟩

section Stable

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

/-- `ψ♯ (x t) = ψ♯ π♯ (x) · t` for the generator `x t` of `A[Jt]`. -/
theorem globalSectionsRingHomSite_algebraBaseChangeMap_reesGenerator
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (ha : Polynomial.monomial 1 a ∈ reesAlgebra J) :
    globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f (reesAlgebra J)
        (basePolynomialRing B S hS T) (reesAlgebra J).val)
        (algebraBaseChangeScalar B S hS T f (reesAlgebra J) ⟨_, ha⟩) =
      globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f (reesAlgebra J)
          (basePolynomialRing B S hS T) (reesAlgebra J).val)
        (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
          (baseScalar f a)) *
        algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) Polynomial.X := by
  refine (globalSectionsRingHomSite_algebraBaseChangeMap_scalar B S hS T f (reesAlgebra J)
    (basePolynomialRing B S hS T) (reesAlgebra J).val ⟨_, ha⟩).trans ?_
  refine (congrArg (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T))
    (Polynomial.C_mul_X_eq_monomial (a := a)).symm).trans ?_
  refine (map_mul (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T))
    (Polynomial.C a) Polynomial.X).trans ?_
  refine congrArg (· * algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T)
    Polynomial.X) ((algebraBaseChangeScalar_polynomial_C B S hS T f J a).trans ?_)
  exact congrArg (fun c => globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f
    (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val)
      (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f (reesAlgebra J)) c))
    (baseScalarRingHom_apply B S hS T f a)

/-- **`Φ : H^p(X_R, G) ⟶ H^p(X, V)` is `R`-equivariant**, `R = A[Jt]` acting on `H^p(X, V)`
through `A[t]`. -/
theorem reesImageCohomology_smul (N : Modules.{u, u} B S hS X.1 X.2)
    (hG : (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N).IsQuasicoherentOnSite) (p : ℕ) (r : reesAlgebra J)
    (z : (modulesCohomologyFunctor B S hS (algebraBaseChange B S hS T f (reesAlgebra J)) p).obj
      (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N)) :
    ((modulesCohomologyFunctor B S hS X p).map (algebraImageModuleι B S hS T f (reesAlgebra J)
        (basePolynomialRing B S hS T) (reesAlgebra J).val N)).hom
      ((cohomologyPushforwardLinearIsoOfIsAffineHom B S hS
        (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
        (isAffineHom_algebraBaseChangeProjection B S hS T f (reesAlgebra J))
        (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
          (reesAlgebra J).val N) hG p).hom.hom
        (algebraBaseChangeScalar B S hS T f (reesAlgebra J) r • z)) =
      reesTotalCohomologyAction B S hS T f J N p ((reesAlgebra J).val r)
        (((modulesCohomologyFunctor B S hS X p).map (algebraImageModuleι B S hS T f
          (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val N)).hom
        ((cohomologyPushforwardLinearIsoOfIsAffineHom B S hS
          (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
          (isAffineHom_algebraBaseChangeProjection B S hS T f (reesAlgebra J))
          (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
            (reesAlgebra J).val N) hG p).hom.hom z)) :=
  cohomologyPushforwardLinearIso_globalSmul_comm B S hS
    (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
    (isAffineHom_algebraBaseChangeProjection B S hS T f (reesAlgebra J))
    (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N) hG
    (algebraImageModuleι B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N)
    (algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N
      (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) ((reesAlgebra J).val r)))
    (algebraBaseChangeScalar B S hS T f (reesAlgebra J) r)
    ((algebraImageModuleι_comp_scalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N (algebraBaseChangeScalar B S hS T f (reesAlgebra J) r)).symm.trans
      (congrArg (fun d => algebraImageModuleι B S hS T f (reesAlgebra J)
        (basePolynomialRing B S hS T) (reesAlgebra J).val N ≫
          algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
            (reesAlgebra J).val N d)
        (globalSectionsRingHomSite_algebraBaseChangeMap_scalar B S hS T f (reesAlgebra J)
          (basePolynomialRing B S hS T) (reesAlgebra J).val r))) p z

end Stable

end AlgebraicGeometry.Space

end
