module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionQuasiCoherentSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DgaResolutionDerivedEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeUnitAlgebra

/-!
# Restriction of scalars along a quasi-isomorphism preserves and reflects quasi-coherence

Let `φ : A ⟶ B` be a unit-preserving homomorphism of sheaves of differential graded algebras.
Restriction of scalars `N ↦ N_A` does not change the underlying complex of sheaves of modules, so
the sections `N_A(U)` over an object `U` are the restriction of the sections `N(U)` along the
homomorphism `φ_U : A(U) ⟶ B(U)` of section algebras, and the restriction maps of `N_A` are those
of `N`. When every `φ_U` is a quasi-isomorphism, derived restriction of scalars along `φ_U` is an
equivalence `D(B(U), d) ≃ D(A(U), d)` (Tag 09S6), and it carries the comparison maps
`N(V) ⊗^𝐋_{B(V)} B(U) ⟶ N(U)` of Definition 24.33.1 to those of `N_A`, up to conjugation by
isomorphisms. So `N_A` satisfies the quasi-coherence condition exactly when `N` does.

On a chaotic site a quasi-isomorphism of sheaves of differential graded algebras — an
isomorphism on cohomology sheaves — is a quasi-isomorphism on the sections over every object, and
the conclusion becomes: derived restriction of scalars `D(B, d) ⥤ D(A, d)` preserves and reflects
`QC(-, d)`. This is the half of Tag 0GZF that does not involve tensor products.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.Hom.sectionHom`: the homomorphism `A(U) ⟶ B(U)` of
  differential graded algebras of sections induced by `φ`.
* `SheafOfModules.DifferentialGradedModule.restrictionSectionModuleIso`: `N_A(U) ≅ N(U)_{A(U)}`.
* `DifferentialGradedModule.derivedRestrictionSquare`: the square of derived restrictions of a
  commutative square of homomorphisms of differential graded algebras over a ring.

## Main results

* `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_fullyFaithful`: adjoint transposes
  through fully faithful functors are invertible together.
* `DifferentialGradedModule.isIso_homEquiv_symm_square_iff`: the comparison maps of a square of
  restrictions along quasi-isomorphisms are invertible together.
* `SheafOfModules.DifferentialGradedModule.isQCModule_restrictionObj_iff`: `N_A` satisfies the
  quasi-coherence condition exactly when `N` does.
* `SheafOfModules.DifferentialGradedAlgebra.Hom.IsQuasiIso.bijective_sectionHom_cohomologyMap`:
  on a chaotic site a quasi-isomorphism is a quasi-isomorphism on sections.
* `SheafOfModules.DifferentialGradedModule.Chaotic.qc_derivedRestriction_iff`: derived
  restriction of scalars along a quasi-isomorphism preserves and reflects `QC(-, d)`.

## References

* [Stacks Project, Lemma 24.34.2 (Tag 0GZF)](https://stacks.math.columbia.edu/tag/0GZF)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Lemma 22.35.6 (Tag 09S6)](https://stacks.math.columbia.edu/tag/09S6)
* [Stacks Project, Example 22.33.2 (Tag 0BYX)](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

/-! ### Adjoint transposes through fully faithful functors -/

namespace CategoryTheory.Adjunction

variable {𝒜₁ 𝒜₂ ℬ₁ ℬ₂ : Type*} [Category 𝒜₁] [Category 𝒜₂] [Category ℬ₁] [Category ℬ₂]

/-- The transpose of `p : X ⟶ G Y` under `F ⊣ G` is invertible exactly when `h ↦ p ≫ G h` is
bijective on every morphism group out of `Y`. -/
theorem isIso_homEquiv_symm_iff_bijective {F : 𝒜₁ ⥤ 𝒜₂} {G : 𝒜₂ ⥤ 𝒜₁} (adj : F ⊣ G) {X : 𝒜₁}
    {Y : 𝒜₂} (p : X ⟶ G.obj Y) :
    IsIso ((adj.homEquiv X Y).symm p) ↔
      ∀ T : 𝒜₂, Function.Bijective (fun h : Y ⟶ T ↦ p ≫ G.map h) := by
  rw [isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun T ↦ ?_
  have key : (fun h : Y ⟶ T ↦ p ≫ G.map h) =
      (adj.homEquiv X T) ∘ (fun h : Y ⟶ T ↦ (adj.homEquiv X Y).symm p ≫ h) := by
    funext h
    simp only [Function.comp_apply, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [key, (adj.homEquiv X T).bijective.of_comp_iff']

/-- Precomposition with an isomorphism is bijective. -/
theorem bijective_iso_hom_comp {X X' Y : 𝒜₁} (e : X ≅ X') :
    Function.Bijective (fun h : X' ⟶ Y ↦ e.hom ≫ h) :=
  (Iso.homFromEquiv e.symm).bijective

/-- Postcomposition with an isomorphism is bijective. -/
theorem bijective_comp_iso_hom {X Y Y' : 𝒜₁} (e : Y ≅ Y') :
    Function.Bijective (fun h : X ⟶ Y ↦ h ≫ e.hom) :=
  (Iso.homToEquiv e).bijective

/-- **Adjoint transposes through fully faithful functors.** Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be
adjunctions, `G₁ : ℬ₁ ⥤ 𝒜₁` and `G₂ : ℬ₂ ⥤ 𝒜₂` fully faithful functors with `G₂` essentially
surjective, and `e : R₂ ⋙ G₁ ≅ G₂ ⋙ R₁`. If `f' : X' ⟶ R₁ Y'` is identified with
`G₁ f : G₁ X ⟶ G₁ (R₂ Y) ≅ R₁ (G₂ Y)` through isomorphisms `X' ≅ G₁ X` and `Y' ≅ G₂ Y`, then the
transpose of `f'` is invertible exactly when the transpose of `f` is. -/
theorem isIso_homEquiv_symm_iff_of_fullyFaithful {L₁ : 𝒜₁ ⥤ 𝒜₂} {R₁ : 𝒜₂ ⥤ 𝒜₁}
    (adj₁ : L₁ ⊣ R₁) {L₂ : ℬ₁ ⥤ ℬ₂} {R₂ : ℬ₂ ⥤ ℬ₁} (adj₂ : L₂ ⊣ R₂) (G₁ : ℬ₁ ⥤ 𝒜₁)
    (G₂ : ℬ₂ ⥤ 𝒜₂) [G₁.Full] [G₁.Faithful] [G₂.Full] [G₂.Faithful] [G₂.EssSurj]
    (e : R₂ ⋙ G₁ ≅ G₂ ⋙ R₁) {X : ℬ₁} {Y : ℬ₂} (f : X ⟶ R₂.obj Y) {X' : 𝒜₁} {Y' : 𝒜₂}
    (f' : X' ⟶ R₁.obj Y') (i : X' ≅ G₁.obj X) (j : Y' ≅ G₂.obj Y)
    (h : f' ≫ R₁.map j.hom = i.hom ≫ G₁.map f ≫ e.hom.app Y) :
    IsIso ((adj₁.homEquiv X' Y').symm f') ↔ IsIso ((adj₂.homEquiv X Y).symm f) := by
  rw [isIso_homEquiv_symm_iff_bijective, isIso_homEquiv_symm_iff_bijective]
  -- the square at a target of the form `G₂ T`
  have hsq : ∀ T : ℬ₂, Function.Bijective (fun k : Y' ⟶ G₂.obj T ↦ f' ≫ R₁.map k) ↔
      Function.Bijective (fun k : Y ⟶ T ↦ f ≫ R₂.map k) := by
    intro T
    have e₁ : (fun k : Y' ⟶ G₂.obj T ↦ f' ≫ R₁.map k) ∘ (fun k : Y ⟶ T ↦ j.hom ≫ G₂.map k) =
        (fun m : X ⟶ R₂.obj T ↦ i.hom ≫ G₁.map m ≫ e.hom.app T) ∘
          (fun k : Y ⟶ T ↦ f ≫ R₂.map k) := by
      funext k
      have hn := e.hom.naturality k
      simp only [Functor.comp_map] at hn
      simp only [Function.comp_apply, Functor.map_comp, Category.assoc]
      rw [reassoc_of% h, ← hn]
    have b₁ : Function.Bijective (fun k : Y ⟶ T ↦ j.hom ≫ G₂.map k) :=
      (bijective_iso_hom_comp j).comp
        ((Functor.FullyFaithful.ofFullyFaithful G₂).map_bijective Y T)
    have b₂ : Function.Bijective (fun m : X ⟶ R₂.obj T ↦ i.hom ≫ G₁.map m ≫ e.hom.app T) :=
      (bijective_iso_hom_comp i).comp ((bijective_comp_iso_hom (e.app T)).comp
        ((Functor.FullyFaithful.ofFullyFaithful G₁).map_bijective X (R₂.obj T)))
    rw [← Function.Bijective.of_comp_iff _ b₁, e₁, Function.Bijective.of_comp_iff' b₂]
  -- the bijectivity only depends on the target up to isomorphism
  have hiso : ∀ {T T' : 𝒜₂} (ε : T ≅ T'),
      Function.Bijective (fun k : Y' ⟶ T ↦ f' ≫ R₁.map k) ↔
        Function.Bijective (fun k : Y' ⟶ T' ↦ f' ≫ R₁.map k) := by
    intro T T' ε
    have e₂ : (fun k : Y' ⟶ T' ↦ f' ≫ R₁.map k) ∘ (fun k : Y' ⟶ T ↦ k ≫ ε.hom) =
        (fun m : X' ⟶ R₁.obj T ↦ m ≫ R₁.map ε.hom) ∘ (fun k : Y' ⟶ T ↦ f' ≫ R₁.map k) := by
      funext k
      simp
    have b₃ : Function.Bijective (fun m : X' ⟶ R₁.obj T ↦ m ≫ R₁.map ε.hom) :=
      bijective_comp_iso_hom (R₁.mapIso ε)
    rw [← Function.Bijective.of_comp_iff _ (bijective_comp_iso_hom ε), e₂,
      Function.Bijective.of_comp_iff' b₃]
  constructor
  · intro H T
    exact (hsq T).1 (H _)
  · intro H T
    exact (hiso (G₂.objObjPreimageIso T)).1 ((hsq _).2 (H _))

end CategoryTheory.Adjunction

/-! ### Derived restriction of scalars on classes of modules -/

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A₁ A₂ : DifferentialGradedAlgebra.{u, u} R}

/-- The class of a module in the derived category. -/
abbrev derivedModuleClass (A₁ : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule.{u, u, u} A₁) :
    derivedCategory' A₁ :=
  (quasiIsomorphisms' A₁).Q.obj ((toHomotopyCategory A₁).obj M)

/-- **Derived restriction of scalars on the class of a module is the class of its restriction**:
`[M_ψ] ≅ R_ψ [M]`. -/
def restrictScalarsClassIso (ψ : A₁.Hom A₂) (M : DifferentialGradedModule.{u, u, u} A₂) :
    derivedModuleClass A₁ (restrictScalars ψ M) ≅
      (derivedRestriction ψ).obj (derivedModuleClass A₂ M) :=
  ((derivedRestrictionFactorization ψ).app ((toHomotopyCategory A₂).obj M)).symm

/-- The identification `restrictScalarsClassIso` is the inverse factorization of derived
restriction. -/
theorem restrictScalarsClassIso_hom (ψ : A₁.Hom A₂) (M : DifferentialGradedModule.{u, u, u} A₂) :
    (restrictScalarsClassIso ψ M).hom =
      (derivedRestrictionFactorization ψ).inv.app ((toHomotopyCategory A₂).obj M) :=
  rfl

/-- The identification of `restrictScalarsClassIso` is natural in the module. -/
theorem restrictScalarsClassIso_naturality (ψ : A₁.Hom A₂)
    {M M' : DifferentialGradedModule.{u, u, u} A₂} (f : M ⟶ M') :
    (quasiIsomorphisms' A₁).Q.map ((toHomotopyCategory A₁).map (restrictScalarsHom ψ f)) ≫
        (restrictScalarsClassIso ψ M').hom =
      (restrictScalarsClassIso ψ M).hom ≫
        (derivedRestriction ψ).map
          ((quasiIsomorphisms' A₂).Q.map ((toHomotopyCategory A₂).map f)) :=
  (derivedRestrictionFactorization ψ).inv.naturality ((toHomotopyCategory A₂).map f)

/-- **Derived restriction of scalars along a quasi-isomorphism is an equivalence**: it is the
right adjoint of derived extension of scalars, which is one by Tag 09S6. -/
theorem isEquivalence_derivedRestriction_of_bijective (ψ : A₁.Hom A₂)
    (h : ∀ k : ℤ, Function.Bijective (ψ.cohomologyMap k)) : (derivedRestriction ψ).IsEquivalence :=
  have := DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_regular ψ h
  (DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
    ψ).isEquivalence_right_of_isEquivalence_left

/-! ### A square of restrictions of scalars -/

section Square

variable {AV AU BV BU : DifferentialGradedAlgebra.{u, u} R} (ρA : AV.Hom AU) (ρB : BV.Hom BU)
  (φV : AV.Hom BV) (φU : AU.Hom BU)
  (hcomm : ∀ x, ρB.toAlgebraHom (φV.toAlgebraHom x) = φU.toAlgebraHom (ρA.toAlgebraHom x))

/-- The identity of the underlying module, from the restriction of `N` along `ρ_B ∘ φ_V` to its
restriction along `φ_U ∘ ρ_A`. -/
def restrictScalarsSquareHom (N : DifferentialGradedModule.{u, u, u} BU) :
    restrictScalars φV (restrictScalars ρB N) ⟶ restrictScalars ρA (restrictScalars φU N) where
  toFun := LinearMap.id
  map_smul x a :=
    congrArg (fun b : BU.A => (MulOpposite.op b • (show N.M from x) : N.M)) (hcomm a)
  map_grading _ _ hx := hx
  map_d := rfl

/-- The identity of the underlying module, from the restriction of `N` along `φ_U ∘ ρ_A` to its
restriction along `ρ_B ∘ φ_V`. -/
def restrictScalarsSquareInv (N : DifferentialGradedModule.{u, u, u} BU) :
    restrictScalars ρA (restrictScalars φU N) ⟶ restrictScalars φV (restrictScalars ρB N) where
  toFun := LinearMap.id
  map_smul x a :=
    congrArg (fun b : BU.A => (MulOpposite.op b • (show N.M from x) : N.M)) (hcomm a).symm
  map_grading _ _ hx := hx
  map_d := rfl

/-- The two restrictions of `N` along the sides of the square agree. -/
def restrictScalarsSquareIso (N : DifferentialGradedModule.{u, u, u} BU) :
    restrictScalars φV (restrictScalars ρB N) ≅ restrictScalars ρA (restrictScalars φU N) where
  hom := restrictScalarsSquareHom ρA ρB φV φU hcomm N
  inv := restrictScalarsSquareInv ρA ρB φV φU hcomm N
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The square of restrictions of scalars on the homotopy categories. -/
def restrictScalarsSquareHomotopyIso :
    restrictScalarsHomotopyFunctor ρB ⋙ restrictScalarsHomotopyFunctor φV ≅
      restrictScalarsHomotopyFunctor φU ⋙ restrictScalarsHomotopyFunctor ρA :=
  NatIso.ofComponents
    (fun X ↦ (toHomotopyCategory AV).mapIso (restrictScalarsSquareIso ρA ρB φV φU hcomm X.as))
    (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨g, rfl⟩ := (toHomotopyCategory BU).map_surjective f
      change (toHomotopyCategory AV).map (restrictScalarsHom φV (restrictScalarsHom ρB g)) ≫
          (toHomotopyCategory AV).map (restrictScalarsSquareHom ρA ρB φV φU hcomm Y) =
        (toHomotopyCategory AV).map (restrictScalarsSquareHom ρA ρB φV φU hcomm X) ≫
          (toHomotopyCategory AV).map (restrictScalarsHom ρA (restrictScalarsHom φU g))
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

/-- The components of `restrictScalarsSquareHomotopyIso` at the classes of modules. -/
theorem restrictScalarsSquareHomotopyIso_hom_app (N : DifferentialGradedModule.{u, u, u} BU) :
    (restrictScalarsSquareHomotopyIso ρA ρB φV φU hcomm).hom.app ((toHomotopyCategory BU).obj N) =
      (toHomotopyCategory AV).map (restrictScalarsSquareHom ρA ρB φV φU hcomm N) :=
  rfl

/-- The square of derived restrictions of a commutative square of homomorphisms of differential
graded algebras, after the localization functor: it is the square of restrictions on the homotopy
categories, read through the factorizations of derived restriction. -/
def derivedRestrictionSquareFactorization :
    (quasiIsomorphisms' BU).Q ⋙ derivedRestriction ρB ⋙ derivedRestriction φV ≅
      (quasiIsomorphisms' BU).Q ⋙ derivedRestriction φU ⋙ derivedRestriction ρA :=
  Functor.isoWhiskerRight (derivedRestrictionFactorization ρB) (derivedRestriction φV) ≪≫
    Functor.isoWhiskerLeft (restrictScalarsHomotopyFunctor ρB)
      (derivedRestrictionFactorization φV) ≪≫
    Functor.isoWhiskerRight (restrictScalarsSquareHomotopyIso ρA ρB φV φU hcomm)
      (quasiIsomorphisms' AV).Q ≪≫
    (Functor.isoWhiskerLeft (restrictScalarsHomotopyFunctor φU)
      (derivedRestrictionFactorization ρA)).symm ≪≫
    (Functor.isoWhiskerRight (derivedRestrictionFactorization φU) (derivedRestriction ρA)).symm

/-- The square of derived restrictions `R_{ρ_B} ⋙ R_{φ_V} ≅ R_{φ_U} ⋙ R_{ρ_A}` of a commutative
square of homomorphisms of differential graded algebras. -/
def derivedRestrictionSquare :
    derivedRestriction ρB ⋙ derivedRestriction φV ≅ derivedRestriction φU ⋙ derivedRestriction ρA :=
  Localization.liftNatIso (quasiIsomorphisms' BU).Q (quasiIsomorphisms' BU)
    ((quasiIsomorphisms' BU).Q ⋙ derivedRestriction ρB ⋙ derivedRestriction φV)
    ((quasiIsomorphisms' BU).Q ⋙ derivedRestriction φU ⋙ derivedRestriction ρA)
    (derivedRestriction ρB ⋙ derivedRestriction φV) (derivedRestriction φU ⋙ derivedRestriction ρA)
    (derivedRestrictionSquareFactorization ρA ρB φV φU hcomm)

/-- The component of `derivedRestrictionSquare` at the class of a module. -/
theorem derivedRestrictionSquare_hom_app (N : DifferentialGradedModule.{u, u, u} BU) :
    (derivedRestrictionSquare ρA ρB φV φU hcomm).hom.app (derivedModuleClass BU N) =
      (derivedRestriction φV).map ((derivedRestrictionFactorization ρB).hom.app
          ((toHomotopyCategory BU).obj N)) ≫
        (derivedRestrictionFactorization φV).hom.app
          ((toHomotopyCategory BV).obj (restrictScalars ρB N)) ≫
        (quasiIsomorphisms' AV).Q.map
          ((toHomotopyCategory AV).map (restrictScalarsSquareHom ρA ρB φV φU hcomm N)) ≫
        (derivedRestrictionFactorization ρA).inv.app
          ((toHomotopyCategory AU).obj (restrictScalars φU N)) ≫
        (derivedRestriction ρA).map ((derivedRestrictionFactorization φU).inv.app
          ((toHomotopyCategory BU).obj N)) := by
  simp [derivedRestrictionSquare, derivedRestrictionSquareFactorization]
  rfl

/-- The component of the square of derived restrictions at the class of a module, through the
identifications of classes of restrictions of scalars. -/
theorem derivedRestrictionSquare_hom_app' (N : DifferentialGradedModule.{u, u, u} BU) :
    (derivedRestrictionSquare ρA ρB φV φU hcomm).hom.app (derivedModuleClass BU N) =
      (derivedRestriction φV).map (restrictScalarsClassIso ρB N).inv ≫
        (restrictScalarsClassIso φV (restrictScalars ρB N)).inv ≫
        (quasiIsomorphisms' AV).Q.map
          ((toHomotopyCategory AV).map (restrictScalarsSquareHom ρA ρB φV φU hcomm N)) ≫
        (restrictScalarsClassIso ρA (restrictScalars φU N)).hom ≫
        (derivedRestriction ρA).map (restrictScalarsClassIso φU N).hom :=
  derivedRestrictionSquare_hom_app ρA ρB φV φU hcomm N

variable {PV : DifferentialGradedModule.{u, u, u} BV} {PU : DifferentialGradedModule.{u, u, u} BU}
  {QV : DifferentialGradedModule.{u, u, u} AV} {QU : DifferentialGradedModule.{u, u, u} AU}
  (mB : PV ⟶ restrictScalars ρB PU) (mA : QV ⟶ restrictScalars ρA QU)
  (iV : QV ≅ restrictScalars φV PV) (iU : QU ≅ restrictScalars φU PU)

/-- The identification `[Q] ≅ R_φ [P]` of a module `Q` with a restriction of scalars of `P`. -/
def restrictScalarsClassIsoOfIso {A₀ B₀ : DifferentialGradedAlgebra.{u, u} R} (ψ : A₀.Hom B₀)
    {P : DifferentialGradedModule.{u, u, u} B₀} {Q : DifferentialGradedModule.{u, u, u} A₀}
    (i : Q ≅ restrictScalars ψ P) :
    derivedModuleClass A₀ Q ≅ (derivedRestriction ψ).obj (derivedModuleClass B₀ P) :=
  (quasiIsomorphisms' A₀).Q.mapIso ((toHomotopyCategory A₀).mapIso i) ≪≫
    restrictScalarsClassIso ψ P

/-- **The derived restriction maps of a square of restrictions.** -/
theorem derivedRestrictionSquare_relation
    (hmod : mA ≫ restrictScalarsHom ρA iU.hom =
      iV.hom ≫ restrictScalarsHom φV mB ≫ restrictScalarsSquareHom ρA ρB φV φU hcomm PU) :
    ((quasiIsomorphisms' AV).Q.map ((toHomotopyCategory AV).map mA) ≫
        (restrictScalarsClassIso ρA QU).hom) ≫
        (derivedRestriction ρA).map (restrictScalarsClassIsoOfIso φU iU).hom =
      (restrictScalarsClassIsoOfIso φV iV).hom ≫
        (derivedRestriction φV).map
          ((quasiIsomorphisms' BV).Q.map ((toHomotopyCategory BV).map mB) ≫
            (restrictScalarsClassIso ρB PU).hom) ≫
        (derivedRestrictionSquare ρA ρB φV φU hcomm).hom.app (derivedModuleClass BU PU) := by
  have n1 := restrictScalarsClassIso_naturality ρA iU.hom
  have n2 := restrictScalarsClassIso_naturality φV mB
  have hm := congrArg (fun f ↦ (quasiIsomorphisms' AV).Q.map ((toHomotopyCategory AV).map f)) hmod
  simp only [Functor.map_comp] at hm
  rw [derivedRestrictionSquare_hom_app']
  simp only [restrictScalarsClassIsoOfIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.map_hom_inv_id_assoc]
  rw [← reassoc_of% n1, ← reassoc_of% n2, Iso.hom_inv_id_assoc, ← reassoc_of% hm]

/-- **The transposes of the two derived restriction maps of a square are invertible together**,
when the two vertical homomorphisms are quasi-isomorphisms. -/
theorem isIso_homEquiv_symm_square_iff
    (hV : ∀ k : ℤ, Function.Bijective (φV.cohomologyMap k))
    (hU : ∀ k : ℤ, Function.Bijective (φU.cohomologyMap k))
    (hmod : mA ≫ restrictScalarsHom ρA iU.hom =
      iV.hom ≫ restrictScalarsHom φV mB ≫ restrictScalarsSquareHom ρA ρB φV φU hcomm PU) :
    IsIso (((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction ρA).homEquiv
        _ _).symm ((quasiIsomorphisms' AV).Q.map ((toHomotopyCategory AV).map mA) ≫
          (restrictScalarsClassIso ρA QU).hom)) ↔
      IsIso (((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction ρB).homEquiv
        _ _).symm ((quasiIsomorphisms' BV).Q.map ((toHomotopyCategory BV).map mB) ≫
          (restrictScalarsClassIso ρB PU).hom)) := by
  have := isEquivalence_derivedRestriction_of_bijective φV hV
  have := isEquivalence_derivedRestriction_of_bijective φU hU
  exact Adjunction.isIso_homEquiv_symm_iff_of_fullyFaithful _ _ _ _
    (derivedRestrictionSquare ρA ρB φV φU hcomm) _ _ (restrictScalarsClassIsoOfIso φV iV)
    (restrictScalarsClassIsoOfIso φU iU)
    (derivedRestrictionSquare_relation ρA ρB φV φU hcomm mB mA iV iU hmod)

end Square

end DifferentialGradedModule

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

/-! ### The homomorphisms of section algebras induced by a homomorphism -/

namespace DifferentialGradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- The map on the sections over `U` of the degree-`n` piece induced by a homomorphism. -/
def Hom.sectionApp (U : Cᵒᵖ) (n : ℤ) :
    A.toGradedAlgebra.sectionsPiece U n →+ B.toGradedAlgebra.sectionsPiece U n :=
  AddMonoidHom.mk' (fun x ↦ (φ.toHomologicalComplex.f n).val.app U x) fun x y ↦ map_add _ x y

/-- The map on sections of a homomorphism, on a section. -/
theorem Hom.sectionApp_apply (U : Cᵒᵖ) (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) :
    φ.sectionApp U n x = (φ.toHomologicalComplex.f n).val.app U x := rfl

/-- The map on the rings of sections over `U`, summand by summand. -/
def Hom.sectionRing (U : Cᵒᵖ) :
    A.toGradedAlgebra.totalSections U →+* B.toGradedAlgebra.totalSections U :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (B.toGradedAlgebra.sectionsPiece U) n).comp (φ.sectionApp U n))
    (by
      change DirectSum.of (B.toGradedAlgebra.sectionsPiece U) 0
          ((φ.toHomologicalComplex.f 0).val.app U (A.one.eval U)) = 1
      rw [hφ U]
      exact DirectSum.of_zero_one _)
    (fun {i j} p q ↦ by
      change DirectSum.of (B.toGradedAlgebra.sectionsPiece U) (i + j)
          ((φ.toHomologicalComplex.f (i + j)).val.app U ((A.mul i j).app U p q)) = _
      rw [φ.map_mul i j U p q]
      exact (GradedAlgebra.of_mul_of_eq B.toGradedAlgebra U i j _ _).symm)

/-- The map on rings of sections, on a summand. -/
@[simp] theorem Hom.sectionRing_of (U : Cᵒᵖ) (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) :
    φ.sectionRing hφ U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n x) =
      DirectSum.of (B.toGradedAlgebra.sectionsPiece U) n (φ.sectionApp U n x) :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of (B.toGradedAlgebra.sectionsPiece U) n).comp (φ.sectionApp U n)) n x

/-- The map on rings of sections commutes with the differentials. -/
theorem Hom.sectionRing_sectionD (U : Cᵒᵖ) (x : A.toGradedAlgebra.totalSections U) :
    φ.sectionRing hφ U (A.sectionD U x) = B.sectionD U (φ.sectionRing hφ U x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      rw [sectionD_of, Hom.sectionRing_of, Hom.sectionRing_of, sectionD_of]
      exact congrArg (DirectSum.of (B.toGradedAlgebra.sectionsPiece U) (n + 1))
        (φ.comm_d_app n U p)

/-- **The homomorphism of differential graded algebras of sections** `A(U) ⟶ B(U)` induced by a
unit-preserving homomorphism `φ : A ⟶ B` of sheaves of differential graded algebras. -/
def Hom.sectionHom (U : Cᵒᵖ) : (A.sectionAlgebra U).Hom (B.sectionAlgebra U) where
  toAlgebraHom := Stacks.uliftIntAlgHom (φ.sectionRing hφ U)
  map_grading := by
    rintro n x ⟨p, rfl⟩
    exact ⟨_, (φ.sectionRing_of hφ U n p).symm⟩
  map_d x := φ.sectionRing_sectionD hφ U x

/-- The homomorphism of section algebras is the map on rings of sections. -/
theorem Hom.sectionHom_apply (U : Cᵒᵖ) (x : (A.sectionAlgebra U).A) :
    (φ.sectionHom hφ U).toAlgebraHom x = φ.sectionRing hφ U x := rfl

/-- **The homomorphisms of section algebras are natural**: they commute with the restriction
homomorphisms. -/
theorem Hom.sectionHom_comp_sectionRestriction {U V : Cᵒᵖ} (a : V ⟶ U) :
    (B.sectionRestriction a).comp (φ.sectionHom hφ V) =
      (φ.sectionHom hφ U).comp (A.sectionRestriction a) := by
  refine _root_.DifferentialGradedAlgebra.Hom.ext_toAlgebraHom (AlgHom.ext fun x ↦ ?_)
  show B.sectionRestrictRing a (φ.sectionRing hφ V x) =
    φ.sectionRing hφ U (A.sectionRestrictRing a x)
  have key : (B.sectionRestrictRing a).comp (φ.sectionRing hφ V) =
      (φ.sectionRing hφ U).comp (A.sectionRestrictRing a) := by
    refine DirectSum.ringHom_ext fun n p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, sectionRestrictRing_of, Hom.sectionRing_of]
    exact congrArg (DirectSum.of (B.toGradedAlgebra.sectionsPiece U) n)
      (PresheafOfModules.naturality_apply (φ.toHomologicalComplex.f n).val a p).symm
  exact DFunLike.congr_fun key x

end DifferentialGradedAlgebra

/-! ### The sections of a restriction of scalars -/

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} (φ : A ⟶ B) (hφ : φ.PreservesOne)
  (N : DifferentialGradedModule.{t, a, a} B)

/-- The right action of the sections of `A` on the sections of `N_A` is the right action of their
images in the sections of `B`. -/
theorem restrictionObj_act (U : Cᵒᵖ) (x : (restrictionObj φ hφ N).totalSections U)
    (s : A.toGradedAlgebra.totalSections U) :
    (restrictionObj φ hφ N).act U x s = N.act U x (φ.sectionRing hφ U s) := by
  have key : (restrictionObj φ hφ N).act U =
      AddMonoidHom.flip ((AddMonoidHom.flip (N.act U)).comp (φ.sectionRing hφ U).toAddMonoidHom) :=
    DirectSum.addHom_ext fun n p ↦ DirectSum.addHom_ext fun i q ↦ by
      show (restrictionObj φ hφ N).act U (DirectSum.of _ n p) (DirectSum.of _ i q) =
        N.act U (DirectSum.of (N.sectionsPiece U) n (show N.sectionsPiece U n from p))
          (φ.sectionRing hφ U (DirectSum.of _ i q))
      rw [DifferentialGradedAlgebra.Hom.sectionRing_of, act_of, actOn_of, act_of, actOn_of]
      rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun key x) s

/-- **The sections of the restriction of `N` are the restriction of the sections of `N`**: the
identity of the group of sections is a homomorphism of differential graded `A(U)`-modules. -/
def restrictionSectionModuleHom (U : Cᵒᵖ) :
    (restrictionObj φ hφ N).sectionModule U ⟶
      _root_.DifferentialGradedModule.restrictScalars (φ.sectionHom hφ U) (N.sectionModule U) where
  toFun := uliftIntLinear (AddMonoidHom.id _)
  map_smul x s := restrictionObj_act φ hφ N U x s
  map_grading _ _ hx := hx
  map_d := rfl

/-- The inverse of `restrictionSectionModuleHom`. -/
def restrictionSectionModuleInv (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.restrictScalars (φ.sectionHom hφ U) (N.sectionModule U) ⟶
      (restrictionObj φ hφ N).sectionModule U where
  toFun := uliftIntLinear (AddMonoidHom.id _)
  map_smul x s := (restrictionObj_act φ hφ N U x s).symm
  map_grading _ _ hx := hx
  map_d := rfl

/-- **The sections of the restriction of `N` are the restriction of the sections of `N`.** -/
def restrictionSectionModuleIso (U : Cᵒᵖ) :
    (restrictionObj φ hφ N).sectionModule U ≅
      _root_.DifferentialGradedModule.restrictScalars (φ.sectionHom hφ U) (N.sectionModule U) where
  hom := restrictionSectionModuleHom φ hφ N U
  inv := restrictionSectionModuleInv φ hφ N U
  hom_inv_id := rfl
  inv_hom_id := rfl

namespace Chaotic

/-- Restriction of sections in the derived category is the class of restriction of sections,
followed by the identification of the class of a restriction of scalars. -/
theorem derivedSectionRestriction_eq (M : DifferentialGradedModule.{t, a, a} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) :
    derivedSectionRestriction M a =
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
            (M.sectionModuleRestriction a)) ≫
        (_root_.DifferentialGradedModule.restrictScalarsClassIso (A.sectionRestriction a)
          (M.sectionModule U)).hom := by
  have hid : (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
      ((_root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
        (A.sectionRestriction a)).inv.app (M.sectionModule U)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) hid).trans (Category.id_comp _))

end Chaotic

/-- **Restriction of scalars along a homomorphism which is a quasi-isomorphism on sections
preserves and reflects the quasi-coherence condition on modules.** -/
theorem isQCModule_restrictionObj_iff
    (h : ∀ (U : Cᵒᵖ) (k : ℤ), Function.Bijective ((φ.sectionHom hφ U).cohomologyMap k)) :
    Chaotic.IsQCModule (restrictionObj φ hφ N) ↔ Chaotic.IsQCModule N := by
  refine forall_congr' fun U ↦ forall_congr' fun V ↦ forall_congr' fun a ↦ ?_
  rw [Chaotic.sectionComparison, Chaotic.sectionComparison, Chaotic.derivedSectionRestriction_eq,
    Chaotic.derivedSectionRestriction_eq]
  exact _root_.DifferentialGradedModule.isIso_homEquiv_symm_square_iff (A.sectionRestriction a)
    (B.sectionRestriction a) (φ.sectionHom hφ V) (φ.sectionHom hφ U)
    (fun x ↦ DFunLike.congr_fun
      (congrArg (·.toAlgebraHom) (φ.sectionHom_comp_sectionRestriction hφ a)) x)
    (N.sectionModuleRestriction a) ((restrictionObj φ hφ N).sectionModuleRestriction a)
    (restrictionSectionModuleIso φ hφ N V) (restrictionSectionModuleIso φ hφ N U) (h V) (h U)
    (_root_.DifferentialGradedModule.Hom.ext (LinearMap.ext fun _ ↦ rfl))

/-- A homomorphism of sheaves of differential graded algebras, read as a homomorphism of right
differential graded `A`-modules from `A` to the restriction of `B`. -/
def regularRestrictionHom :
    regularModule A ⟶ restrictionObj φ hφ (regularModule B) where
  toHomologicalComplex := φ.toHomologicalComplex
  map_mul n i U x y := φ.map_mul n i U x y

/-- The right action of the sections of `A` on the sections of the regular module is the
multiplication of the section algebra. -/
theorem regularModule_act (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ)
    (x s : A.toGradedAlgebra.totalSections U) :
    (regularModule A).act U x s = x * s := by
  have key : (regularModule A).act U = AddMonoidHom.mk'
      (fun x ↦ AddMonoidHom.mk' (fun s ↦ (show A.toGradedAlgebra.totalSections U from x) * s)
        (fun s s' ↦ mul_add _ s s'))
      (fun x y ↦ AddMonoidHom.ext fun s ↦
        add_mul (show A.toGradedAlgebra.totalSections U from x) (show _ from y) s) :=
    DirectSum.addHom_ext fun n p ↦ DirectSum.addHom_ext fun i q ↦ by
      show (regularModule A).act U (DirectSum.of _ n p) (DirectSum.of _ i q) =
        DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n
            (show A.toGradedAlgebra.sectionsPiece U n from p) *
          DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i q
      rw [act_of, actOn_of, GradedAlgebra.of_mul_of_eq]
      rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun key x) s

/-- **The sections of the regular module are the regular module of the section algebra.** -/
def regularSectionModuleIso (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    (regularModule A).sectionModule U ≅
      _root_.DifferentialGradedModule.regularModule (A.sectionAlgebra U) where
  hom :=
    { toFun := uliftIntLinear (AddMonoidHom.id _)
      map_smul x s := regularModule_act A U x s
      map_grading _ _ hx := hx
      map_d := rfl }
  inv :=
    { toFun := uliftIntLinear (AddMonoidHom.id _)
      map_smul x s := (regularModule_act A U x s).symm
      map_grading _ _ hx := hx
      map_d := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The map of sections induced by `regularRestrictionHom` is the homomorphism of section
algebras, read as a homomorphism of regular modules. -/
theorem sectionMap_regularRestrictionHom (U : Cᵒᵖ) :
    sectionMap (regularRestrictionHom φ hφ) U ≫
        (restrictionSectionModuleIso φ hφ (regularModule B) U).hom ≫
          _root_.DifferentialGradedModule.restrictScalarsHom (φ.sectionHom hφ U)
            (regularSectionModuleIso B U).hom =
      (regularSectionModuleIso A U).hom ≫ (φ.sectionHom hφ U).toRegularRestriction := by
  refine _root_.DifferentialGradedModule.Hom.ext (LinearMap.ext fun x ↦ ?_)
  show sectionMapAdd (regularRestrictionHom φ hφ) U x = φ.sectionRing hφ U x
  have key : sectionMapAdd (regularRestrictionHom φ hφ) U =
      (φ.sectionRing hφ U).toAddMonoidHom :=
    DirectSum.addHom_ext fun n p ↦ by
      show sectionMapAdd (regularRestrictionHom φ hφ) U (DirectSum.of _ n p) =
        φ.sectionRing hφ U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n
          (show A.toGradedAlgebra.sectionsPiece U n from p))
      rw [sectionMapAdd_of, DifferentialGradedAlgebra.Hom.sectionRing_of]
      rfl
  exact DFunLike.congr_fun key x

end DifferentialGradedModule

/-! ### A quasi-isomorphism on a chaotic site is a quasi-isomorphism on sections -/

namespace DifferentialGradedAlgebra

section Chaotic

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {φ : A ⟶ B} (hφ : φ.PreservesOne)

/-- **On a chaotic site, a homomorphism of sheaves of differential graded algebras inducing an
isomorphism on cohomology sheaves induces an isomorphism on the cohomology of the differential
graded algebras of sections over every object.** Sheafification being the identity, the
cohomology sheaves are computed sectionwise. -/
theorem Hom.IsQuasiIso.bijective_sectionHom_cohomologyMap (hqis : φ.IsQuasiIso) (U : Cᵒᵖ)
    (k : ℤ) : Function.Bijective ((φ.sectionHom hφ U).cohomologyMap k) := by
  have h := DifferentialGradedModule.quasiIso_sectionMap
    (DifferentialGradedModule.regularRestrictionHom φ hφ) U hqis
  have e := DifferentialGradedModule.sectionMap_regularRestrictionHom φ hφ U
  replace h := (quasiIso_iff_of_arrow_mk_iso _ _
    ((_root_.DifferentialGradedModule.forgetToCochainComplex (A.sectionAlgebra U)).mapArrow.mapIso
      (Arrow.isoMk (f := Arrow.mk (DifferentialGradedModule.sectionMap
          (DifferentialGradedModule.regularRestrictionHom φ hφ) U))
        (g := Arrow.mk (φ.sectionHom hφ U).toRegularRestriction)
        (DifferentialGradedModule.regularSectionModuleIso A U)
        (DifferentialGradedModule.restrictionSectionModuleIso φ hφ _ U ≪≫
          (_root_.DifferentialGradedModule.restrictScalarsFunctor (φ.sectionHom hφ U)).mapIso
            (DifferentialGradedModule.regularSectionModuleIso B U)) e.symm))).1 h
  exact _root_.DifferentialGradedAlgebra.Hom.bijective_cohomologyMap_of_quasiIso
    (φ.sectionHom hφ U) h k

end Chaotic

end DifferentialGradedAlgebra

/-! ### Derived restriction of scalars along a quasi-isomorphism and `QC(-, d)` -/

namespace DifferentialGradedModule

namespace Chaotic

section Derived

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{u} C] {O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {A B : DifferentialGradedAlgebra.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chaoticRingedSite O).O)}

variable (A) in
/-- **The class of a module lies in `QC(A, d)` exactly when the module satisfies the
quasi-coherence condition.** -/
theorem qc_derivedClass_iff (M : DifferentialGradedModule.{u, v, v} A) :
    QC A (derivedClass A M) ↔ IsQCModule M :=
  (qc_iff_forall_transposeLocus A _).trans
    (forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun a ↦
      (isIso_sectionComparison_iff A M a).symm)

/-- **Restriction of scalars `D(B, d) ⥤ D(A, d)` along a quasi-isomorphism of sheaves of
differential graded algebras on a chaotic site preserves and reflects quasi-coherence.** -/
theorem qc_derivedRestriction_iff (φ : A ⟶ B) (hφ : φ.PreservesOne) (hqis : φ.IsQuasiIso)
    (X : derivedCategory.{u, v, v} B) :
    QC A ((derivedRestriction.{u, v, v} φ hφ).obj X) ↔ QC B X := by
  obtain ⟨N, rfl⟩ := exists_module_eq B X
  have e : (derivedRestriction.{u, v, v} φ hφ).obj (derivedClass B N) ≅
      derivedClass A (restrictionObj φ hφ N) :=
    (derivedRestrictionIso.{u, v, v} φ hφ).app ((HomotopyCategory.quotient B).obj N)
  rw [(QC A).prop_iff_of_iso e, qc_derivedClass_iff B N]
  exact (qc_derivedClass_iff A (restrictionObj φ hφ N)).trans
    (isQCModule_restrictionObj_iff φ hφ N fun U k ↦
      hqis.bijective_sectionHom_cohomologyMap hφ U k)

end Derived

end Chaotic

end DifferentialGradedModule

end SheafOfModules

end
