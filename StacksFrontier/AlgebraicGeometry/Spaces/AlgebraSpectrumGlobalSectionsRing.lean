module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSpectrumBaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedFibreIdeal

/-!
# Global functions of the spectrum of an algebra, and of base changes to it

For an affine object `T` of the site with `A = Γ(T₀, ⊤)` and a finitely generated `A`-algebra
`R`, the global functions of the space `h_{Spec R}` are `R`.  Through this identification:

* the morphism `h_{Spec R} ⟶ h_T` induces `algebraMap A R`, and the morphism
  `h_{Spec R'} ⟶ h_{Spec R}` attached to an `A`-algebra map `φ : R ⟶ R'` induces `φ`;
* on the base change `X_R = X ×_{h_T} h_{Spec R}` of `f : X ⟶ h_T`, the global functions coming
  from `R` (`AlgebraicGeometry.Space.algebraBaseChangeScalar`) are compatible with the map
  `X_{R'} ⟶ X_R` and with the global functions coming from `A` through `f`
  (`AlgebraicGeometry.Space.baseScalar`).

## Main definitions

* `AlgebraicGeometry.Space.schemeSpaceGlobalSectionsEquiv`: `Γ(h_U, 𝒪) ≃+* Γ(U₀, ⊤)`.
* `AlgebraicGeometry.Space.algebraSpectrumGlobalSectionsEquiv`: `Γ(h_{Spec R}, 𝒪) ≃+* R`.
* `AlgebraicGeometry.Space.algebraBaseChangeScalar`: `R →+* Γ(X_R, 𝒪)`.

## Main results

* `AlgebraicGeometry.Space.schemeSpaceGlobalSectionsEquiv_globalSectionsRingHomSite`: the ring
  map of global functions of a morphism of represented spaces is `Γ` of the morphism.
* `AlgebraicGeometry.Space.globalSectionsRingHomSite_algebraBaseChangeMap_scalar`:
  `ψ♯ ∘ (R ⟶ Γ(X_R)) = (R' ⟶ Γ(X_{R'})) ∘ φ`.
* `AlgebraicGeometry.Space.algebraBaseChangeScalar_algebraMap`: `A ⟶ R ⟶ Γ(X_R)` is
  `π♯ ∘ baseScalar`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `Γ(h_U, 𝒪) ≃+* Γ(U₀, ⊤)`: evaluation at the terminal identity chart. -/
def schemeSpaceGlobalSectionsEquiv (U : BigFppfOver B S hS) :
    RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O).obj ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  globalSectionsChartRingEquiv B S hS (schemeSpace U) (isTerminalIdEtaleChart B S hS U)

/-- `schemeSpaceGlobalSectionsEquiv` evaluates a global function at the identity chart. -/
theorem schemeSpaceGlobalSectionsEquiv_apply (U : BigFppfOver B S hS)
    (a : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O).obj) :
    schemeSpaceGlobalSectionsEquiv B S hS U a = a.1 (op (idEtaleChart B S hS U)) :=
  rfl

/-- The ring map of global functions of `h_g : h_U ⟶ h_W` is `Γ(g)`. -/
theorem schemeSpaceGlobalSectionsEquiv_globalSectionsRingHomSite {U W : BigFppfOver B S hS}
    (g : U ⟶ W)
    (a : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace W).1 (schemeSpace W).2).O).obj) :
    schemeSpaceGlobalSectionsEquiv B S hS U
        (globalSectionsRingHomSite B S hS (schemeSpaceMap g) a) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        (schemeSpaceGlobalSectionsEquiv B S hS W a) :=
  (globalSectionsRingHomSite_val_chartDiagram B S hS (schemeSpaceMap g) a
    ⟨idEtaleChart B S hS U, idEtaleChart B S hS W, g,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩).trans rfl

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- `Γ(h_{Spec R}, 𝒪) ≃+* R`. -/
def algebraSpectrumGlobalSectionsEquiv (R : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R] :
    RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (schemeSpace (algebraSpectrumOver B S hS T R)).1
        (schemeSpace (algebraSpectrumOver B S hS T R)).2).O).obj ≃+* R :=
  (schemeSpaceGlobalSectionsEquiv B S hS (algebraSpectrumOver B S hS T R)).trans
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv

/-- `Γ(Spec R ⟶ T₀)` read through `Γ(Spec R, ⊤) ≅ R` is the structure map `A ⟶ R`. -/
theorem algebraSpectrumMap_appTop_apply (R : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (Scheme.ΓSpecIso (.of R)).hom.hom ((algebraSpectrumMap B S hS T R).appTop.hom a) =
      algebraMap _ R a := by
  have h : (algebraSpectrumMap B S hS T R).appTop ≫ (Scheme.ΓSpecIso (.of R)).hom =
      CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R) := by
    rw [algebraSpectrumMap, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
      ← Category.assoc]
    have e : ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))).hom =
          𝟙 _ := by
      have h1 : (Scheme.ΓSpecIso (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))).hom =
          ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ.appTop :=
        (Scheme.toSpecΓ_appTop _).symm
      rw [h1, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv]
      rfl
    rw [e, Category.id_comp]
  exact congrArg (fun m => m.hom a) h

/-- The morphism `h_{Spec R} ⟶ h_T` induces `algebraMap A R` on global functions. -/
theorem algebraSpectrumGlobalSectionsEquiv_siteHom (R : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    (a : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O).obj) :
    algebraSpectrumGlobalSectionsEquiv B S hS T R
        (globalSectionsRingHomSite B S hS (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R)) a) =
      algebraMap _ R (schemeSpaceGlobalSectionsEquiv B S hS T a) := by
  show (Scheme.ΓSpecIso (.of R)).hom.hom (schemeSpaceGlobalSectionsEquiv B S hS _
    (globalSectionsRingHomSite B S hS (schemeSpaceMap (algebraSpectrumSiteHom B S hS T R)) a)) = _
  rw [schemeSpaceGlobalSectionsEquiv_globalSectionsRingHomSite]
  exact algebraSpectrumMap_appTop_apply B S hS T R _

/-- The morphism `h_{Spec R'} ⟶ h_{Spec R}` attached to `φ : R ⟶ R'` induces `φ` on global
functions. -/
theorem algebraSpectrumGlobalSectionsEquiv_siteMap (R : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    (R' : Type u) [CommRing R'] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R')
    (a : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (schemeSpace (algebraSpectrumOver B S hS T R)).1
        (schemeSpace (algebraSpectrumOver B S hS T R)).2).O).obj) :
    algebraSpectrumGlobalSectionsEquiv B S hS T R'
        (globalSectionsRingHomSite B S hS
          (schemeSpaceMap (algebraSpectrumSiteMap B S hS T R R' φ)) a) =
      φ (algebraSpectrumGlobalSectionsEquiv B S hS T R a) := by
  show (Scheme.ΓSpecIso (.of R')).hom.hom (schemeSpaceGlobalSectionsEquiv B S hS _
    (globalSectionsRingHomSite B S hS
      (schemeSpaceMap (algebraSpectrumSiteMap B S hS T R R' φ)) a)) = _
  rw [schemeSpaceGlobalSectionsEquiv_globalSectionsRingHomSite]
  exact congrArg (fun m => m.hom (schemeSpaceGlobalSectionsEquiv B S hS _ a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))

variable {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]

/-- The global functions of `X_R` coming from `R`: `R ≅ Γ(h_{Spec R}) ⟶ Γ(X_R)`. -/
def algebraBaseChangeScalar :
    R →+* RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2).O).obj :=
  (globalSectionsRingHomSite B S hS (algebraBaseChangeStructure B S hS T f R)).comp
    (algebraSpectrumGlobalSectionsEquiv B S hS T R).symm.toRingHom

/-- `algebraBaseChangeScalar` is `Γ` of the structure morphism `X_R ⟶ h_{Spec R}` applied to the
inverse of `algebraSpectrumGlobalSectionsEquiv`. -/
theorem algebraBaseChangeScalar_apply (r : R) :
    algebraBaseChangeScalar B S hS T f R r =
      globalSectionsRingHomSite B S hS (algebraBaseChangeStructure B S hS T f R)
        ((algebraSpectrumGlobalSectionsEquiv B S hS T R).symm r) :=
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- `AlgebraicGeometry.Space.baseScalar f` is `Γ(f)` applied to the inverse of
`AlgebraicGeometry.Space.schemeSpaceGlobalSectionsEquiv`. -/
theorem baseScalar_eq_globalSectionsRingHomSite (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    baseScalar f a =
      globalSectionsRingHomSite B S hS f ((schemeSpaceGlobalSectionsEquiv B S hS T).symm a) := by
  unfold baseScalar
  congr 1

/-- A commuting square of morphisms of algebraic spaces gives equal composites of the ring maps of
global functions. -/
private theorem globalSectionsRingHomSite_comm_apply {X Y₁ Y₂ Z : AlgebraicSpaces B S hS}
    (f₁ : X ⟶ Y₁) (g₁ : Y₁ ⟶ Z) (f₂ : X ⟶ Y₂) (g₂ : Y₂ ⟶ Z) (h : f₁ ≫ g₁ = f₂ ≫ g₂)
    (x : RingCat.sectionsSubring
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj) :
    globalSectionsRingHomSite B S hS f₁ (globalSectionsRingHomSite B S hS g₁ x) =
      globalSectionsRingHomSite B S hS f₂ (globalSectionsRingHomSite B S hS g₂ x) := by
  have h' := congrArg (fun k => globalSectionsRingHomSite B S hS k x) h
  rwa [globalSectionsRingHomSite_comp, globalSectionsRingHomSite_comp, RingHom.comp_apply,
    RingHom.comp_apply] at h'

/-- For `ψ : X_{R'} ⟶ X_R` attached to `φ : R ⟶ R'`, `ψ♯ (r) = φ (r)` on the global functions
coming from `R` and `R'`. -/
theorem globalSectionsRingHomSite_algebraBaseChangeMap_scalar (R' : Type u) [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R') (r : R) :
    globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ)
        (algebraBaseChangeScalar B S hS T f R r) =
      algebraBaseChangeScalar B S hS T f R' (φ r) := by
  rw [algebraBaseChangeScalar_apply, algebraBaseChangeScalar_apply,
    globalSectionsRingHomSite_comm_apply B S hS _ _ _ _
      (algebraBaseChangeMap_structure B S hS T f R R' φ)]
  congr 1
  refine (algebraSpectrumGlobalSectionsEquiv B S hS T R').injective ?_
  rw [RingEquiv.apply_symm_apply, algebraSpectrumGlobalSectionsEquiv_siteMap,
    RingEquiv.apply_symm_apply]

/-- The global functions of `X_R` coming from `A` through `R` are those coming from `A` through
`X`: `(A ⟶ R ⟶ Γ(X_R)) = π♯ ∘ baseScalar`. -/
theorem algebraBaseChangeScalar_algebraMap (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    algebraBaseChangeScalar B S hS T f R (algebraMap _ R a) =
      globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R)
        (baseScalar f a) := by
  rw [baseScalar_eq_globalSectionsRingHomSite,
    globalSectionsRingHomSite_comm_apply B S hS _ _ _ _ pullback.condition,
    algebraBaseChangeScalar_apply]
  congr 1
  refine (algebraSpectrumGlobalSectionsEquiv B S hS T R).injective ?_
  rw [RingEquiv.apply_symm_apply, algebraSpectrumGlobalSectionsEquiv_siteHom]
  exact congrArg (algebraMap _ R) (RingEquiv.apply_symm_apply _ a).symm

end AlgebraicGeometry.Space

end
