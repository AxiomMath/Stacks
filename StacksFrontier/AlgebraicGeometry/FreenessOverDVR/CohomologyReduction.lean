module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.AdicMultiplication
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.LengthTransfer
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.Triviality
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# The cohomology of `πᵏ F` modulo `πᵐ`

Let `A` be a ring, `f : X ⟶ Spec A`, `π ∈ A` and `F` a quasi-coherent module on `X` whose stalks
have `π`-torsion of exponent at most `k`. The short exact sequence
`0 → πᵏ F --πᵐ--> πᵏ F → πᵏ (F / πᵏ⁺ᵐ F) → 0` of
`Stacks.AlgebraicGeometry.FreenessOverDVR.adicReductionComplex_shortExact` has a long exact
cohomology sequence in which the maps induced by multiplication by `πᵐ` are multiplication by
`πᵐ`. Over a discrete valuation ring with `f` proper and `F` coherent this computes the length
of `H⁰(X, πᵏ (F / πᵏ⁺ᵐ F))` as the length of `H⁰(X, πᵏ F) ⧸ πᵐ` plus that of
`H¹(X, πᵏ F)[πᵐ]`, and the left-hand side only depends on `F / πᵏ⁺ᵐ F`.

## Main definitions

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `cohomologyMap`, `cohomologyδ`: the maps of the long exact cohomology sequence, as `A`-linear
  maps between the modules `cohomologyOver A f i F`.

## Main results

* `cohomologyMap_globalSmul`: multiplication by `πⁿ` on `F` induces multiplication by `πⁿ` on
  cohomology.
* `moduleFinite_cohomologyOver`: [Stacks, Tag 02O6] in the spelling `cohomologyOver`.
* `length_cohomology_adicImage`: the length of `H⁰(X, πᵏ (F / πᵏ⁺ᵐ F))`.
* `adicImageIso`, `adicQuotientIsoOfLE`: an isomorphism `F / πⁿ F ≅ G / πⁿ G` induces the
  corresponding isomorphisms for every smaller exponent and for the images of `πᵏ`.
* `torsionBy_cohomology_eq_bot_of_adicQuotientIso`: **the torsion exponent of `H¹(X, πᵏ E)` is
  read off `E / πⁿ E`**, for `n ≥ k + e + 1`.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.BaseAdicFiltration Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### The long exact sequence as `A`-linear maps -/

/-- The `A`-linear map `Hⁱ(X, F) ⟶ Hⁱ(X, G)` induced by a morphism of modules. -/
def cohomologyMap (i : ℕ) {F G : X.Modules} (φ : F ⟶ G) :
    cohomologyOver A f i F →ₗ[A] cohomologyOver A f i G :=
  ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).map φ)).hom

/-- `cohomologyMap` evaluates as the map of the right derived functor of global sections. -/
theorem cohomologyMap_apply (i : ℕ) {F G : X.Modules} (φ : F ⟶ G)
    (c : cohomologyOver A f i F) :
    cohomologyMap A f i φ c =
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).map φ).hom c :=
  rfl

/-- `cohomologyMap` sends a composite of module maps to the composite of the induced maps. -/
theorem cohomologyMap_comp (i : ℕ) {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) :
    cohomologyMap A f i (φ ≫ ψ) = (cohomologyMap A f i ψ).comp (cohomologyMap A f i φ) := by
  ext c
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).map_comp φ ψ)) c

/-- `cohomologyMap` sends the identity of a module to the identity. -/
theorem cohomologyMap_id (i : ℕ) (F : X.Modules) :
    cohomologyMap A f i (𝟙 F) = LinearMap.id := by
  ext c
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).map_id F)) c

/-- **Multiplication by `πⁿ` induces multiplication by `πⁿ` on cohomology.** The right derived
functors of global sections are `Γ(X, ⊤)`-linear, and the `A`-module structure on cohomology is
read through `A → Γ(X, ⊤)`. -/
theorem cohomologyMap_globalSmul (i : ℕ) (a : A) (n : ℕ) (F : X.Modules) :
    cohomologyMap A f i (globalSmul (baseScalarMap f a ^ n) F) = a ^ n • LinearMap.id := by
  ext c
  have hlin : ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).map
      (globalSmul (baseScalarMap f a ^ n) F) = (baseScalarMap f a ^ n) • 𝟙 _ := by
    rw [globalSmul_eq_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [cohomologyMap_apply, hlin, LinearMap.smul_apply, LinearMap.id_apply,
    ModuleCat.restrictScalars.smul_def, ← map_pow]
  rfl

variable {A f} in
/-- The connecting map `Hⁱ(X, S.X₃) ⟶ Hⁱ⁺¹(X, S.X₁)` of a short exact sequence, `A`-linearly. -/
def cohomologyδ {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ) :
    cohomologyOver A f i S.X₃ →ₗ[A] cohomologyOver A f (i + 1) S.X₁ :=
  ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).δ hS i)).hom

/-- `cohomologyδ` evaluates as the connecting map of the cohomology δ-functor. -/
theorem cohomologyδ_apply {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ)
    (c : cohomologyOver A f i S.X₃) :
    cohomologyδ (A := A) (f := f) hS i c =
      ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).δ hS i).hom c :=
  rfl

/-- The long exact cohomology sequence of `S` is exact at `Hⁱ(X, S.X₂)`. -/
theorem exact_cohomologyMap {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ) :
    Function.Exact (cohomologyMap A f i S.f) (cohomologyMap A f i S.g) := fun c =>
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).exact_map hS i) c

/-- The long exact cohomology sequence of `S` is exact at `Hⁱ(X, S.X₃)`. -/
theorem exact_cohomologyMap_δ {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ) :
    Function.Exact (cohomologyMap A f i S.g) (cohomologyδ (A := A) (f := f) hS i) := fun c =>
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).exact_δ₁ hS i) c

/-- The long exact cohomology sequence of `S` is exact at `Hⁱ⁺¹(X, S.X₁)`. -/
theorem exact_cohomologyδ_map {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ) :
    Function.Exact (cohomologyδ (A := A) (f := f) hS i) (cohomologyMap A f (i + 1) S.f) :=
  fun c => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).exact_δ₂ hS i) c

/-- The connecting map `cohomologyδ` is natural in the short exact sequence. -/
theorem cohomologyδ_naturality {S T : ShortComplex X.Modules} (hS : S.ShortExact)
    (hT : T.ShortExact) (φ : S ⟶ T) (i : ℕ) (c : cohomologyOver A f i S.X₃) :
    cohomologyδ (A := A) (f := f) hT i (cohomologyMap A f i φ.τ₃ c) =
      cohomologyMap A f (i + 1) φ.τ₁ (cohomologyδ (A := A) (f := f) hS i c) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).δ_naturality hS hT φ i)) c

/-! ### Finiteness -/

/-- **[Stacks, Tag 02O6]** in the spelling `cohomologyOver`: for `f` proper over a Noetherian
ring and `F` coherent, `Hⁱ(X, F)` is a finite `A`-module. -/
theorem moduleFinite_cohomologyOver [IsNoetherianRing A] [IsProper f] (F : X.Modules)
    [F.IsCoherent] (i : ℕ) : Module.Finite A (cohomologyOver A f i F) := by
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology f F i
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hsurj
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).obj F))

/-! ### The length of `H⁰(X, πᵏ (F / πᵏ⁺ᵐ F))` -/

variable (π : A)

/-- On the zeroth cohomology of `πᵏ F`, multiplication by `πᵐ` is injective, once the stalks of
`F` have `π`-torsion of exponent at most `k`: the zeroth right derived functor preserves the
monomorphism of `adicReductionComplex_shortExact`. -/
theorem injective_cohomology_adicReduction (F : X.Modules) [F.IsQuasicoherent] {k : ℕ}
    (hk : StalkTorsionBounded F (baseScalarMap f π) k) (m : ℕ) :
    Function.Injective (cohomologyMap A f 0 (adicReductionComplex f π F k m).f) :=
  (ModuleCat.mono_iff_injective (((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor
    X).functor 0).map (adicReductionComplex f π F k m).f)).1
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor X).mono_map_f
      (adicReductionComplex_shortExact f π F hk m))

/-- **The length of `H⁰(X, πᵏ (F / πᵏ⁺ᵐ F))`**: once the stalks of `F` have `π`-torsion of
exponent at most `k`, it is the length of `H⁰(X, πᵏ F) ⧸ πᵐ` plus that of `H¹(X, πᵏ F)[πᵐ]`. -/
theorem length_cohomology_adicImage (F : X.Modules) [F.IsQuasicoherent] {k : ℕ}
    (hk : StalkTorsionBounded F (baseScalarMap f π) k) (m : ℕ) :
    Module.length A (cohomologyOver A f 0 (adicImage f π F k m).toSheafOfModules) =
      Module.length A (cohomologyOver A f 0
          (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules ⧸
        Ideal.span {π} ^ m • (⊤ : Submodule A (cohomologyOver A f 0
          (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules))) +
        Module.length A (Submodule.torsionBy A (cohomologyOver A f 1
          (adicFiltration f (Ideal.span {π}) k F).toSheafOfModules) (π ^ m)) := by
  have hS := adicReductionComplex_shortExact f π F hk m
  have hf : ∀ i, cohomologyMap A f i (adicReductionComplex f π F k m).f = π ^ m • LinearMap.id :=
    fun i => cohomologyMap_globalSmul A f i π m _
  have h₁ := exact_cohomologyMap A f hS 0
  have h₃ := exact_cohomologyδ_map A f hS 0
  rw [hf] at h₁ h₃
  exact length_eq_length_quotient_add_length_torsionBy m _ _ h₁ (exact_cohomologyMap_δ A f hS 0)
    h₃

/-! ### Only `F / πᵏ⁺ᵐ F` matters -/

variable {A f π} in
/-- An isomorphism `F / πᵏ⁺ᵐ F ≅ G / πᵏ⁺ᵐ G` restricts to `πᵏ (F / πᵏ⁺ᵐ F) ≅ πᵏ (G / πᵏ⁺ᵐ G)`. -/
def adicImageIso {F G : X.Modules} {k m : ℕ}
    (e : adicQuotient f (Ideal.span {π}) (k + m) F ≅ adicQuotient f (Ideal.span {π}) (k + m) G) :
    ((adicImage f π F k m).toSheafOfModules : X.Modules) ≅
      ((adicImage f π G k m).toSheafOfModules : X.Modules) where
  hom := sheafSubmoduleMap e.hom _ _ (idealPowerMultiple_le_sheafSubmoduleComap _ k e.hom _ le_rfl)
  inv := sheafSubmoduleMap e.inv _ _ (idealPowerMultiple_le_sheafSubmoduleComap _ k e.inv _ le_rfl)
  hom_inv_id := by
    refine (Scheme.Modules.mono_submodule_ι (adicImage f π F k m)).right_cancellation _ _ ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (sheafSubmoduleMap_comp_ι _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ e.inv) (sheafSubmoduleMap_comp_ι _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (_ ≫ ·) e.hom_inv_id).trans ((Category.comp_id _).trans
      (Category.id_comp _).symm)
  inv_hom_id := by
    refine (Scheme.Modules.mono_submodule_ι (adicImage f π G k m)).right_cancellation _ _ ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (sheafSubmoduleMap_comp_ι _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ e.hom) (sheafSubmoduleMap_comp_ι _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (_ ≫ ·) e.inv_hom_id).trans ((Category.comp_id _).trans
      (Category.id_comp _).symm)

variable {A f π} in
/-- An isomorphism `F / πⁿ F ≅ G / πⁿ G` induces `F / πʲ F ≅ G / πʲ G` for every `j ≤ n`. -/
def adicQuotientIsoOfLE {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] {j n : ℕ}
    (h : j ≤ n)
    (φ : adicQuotient f (Ideal.span {π}) n F ≅ adicQuotient f (Ideal.span {π}) n G) :
    adicQuotient f (Ideal.span {π}) j F ≅ adicQuotient f (Ideal.span {π}) j G :=
  haveI := isIso_idealPowerQuotientMap_of_cokernel_π_comp (baseIdeal f (Ideal.span {π}))
    (baseIdeal f (Ideal.span {π})) j n (Scheme.IdealSheafData.pow_le_pow_of_le _ h) φ
    (adicProj f (Ideal.span {π}) n F ≫ φ.hom) rfl
  haveI := isIso_idealPowerQuotientMap_cokernel_π (baseIdeal f (Ideal.span {π}))
    (baseIdeal f (Ideal.span {π})) j n (Scheme.IdealSheafData.pow_le_pow_of_le _ h) G
  asIso (idealPowerQuotientMap _ _ j j le_rfl (adicProj f (Ideal.span {π}) n F ≫ φ.hom)) ≪≫
    (asIso (idealPowerQuotientMap _ _ j j le_rfl (adicProj f (Ideal.span {π}) n G))).symm

variable {A f} in
/-- An isomorphism of modules induces an `A`-linear equivalence on cohomology. -/
def cohomologyLinearEquiv (i : ℕ) {F G : X.Modules} (e : F ≅ G) :
    cohomologyOver A f i F ≃ₗ[A] cohomologyOver A f i G :=
  ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapIso
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).mapIso e)).toLinearEquiv

/-! ### The transfer of the torsion exponent -/

/-- The sheaf `πᵏ F` of a coherent module on a locally Noetherian scheme is coherent. -/
theorem isCoherent_adicFiltration [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (k : ℕ) : ((adicFiltration f (Ideal.span {π}) k F).toSheafOfModules : X.Modules).IsCoherent :=
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have := Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple
    (baseIdeal f (Ideal.span {π})) k F
  Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono
    (adicFiltration f (Ideal.span {π}) k F).ι

/-- **The torsion exponent of `H¹(X, πᵏ E)` is read off `E / πⁿ E`.** Let `A` be a discrete
valuation ring with uniformizer `π`, `f : X ⟶ Spec A` proper and `E`, `G` coherent with stalks of
`π`-torsion exponent at most `k`. Suppose `E / πⁿ E ≅ G / πⁿ G` for some `n ≥ k + e + 1`, that
`H⁰(X, πᵏ E)` and `H⁰(X, πᵏ G)` have the same free rank, and that `πᵉ` kills the
`πᵉ⁺¹`-torsion of `H¹(X, πᵏ G)`. Then `πᵉ` kills the `πᵉ⁺¹`-torsion of `H¹(X, πᵏ E)`.

The two exponents `e` and `e + 1` of the reduction `0 → πᵏ F --πᵐ--> πᵏ F → πᵏ (F / πᵏ⁺ᵐ F) → 0`
compare the lengths of the extensions `H⁰(X, πᵏ (F / πᵏ⁺ᵐ F))`, which depend only on
`F / πⁿ F`, and `pow_smul_torsionBy_eq_bot_of_length_eq` turns that comparison into the bound. -/
theorem torsionBy_cohomology_eq_bot_of_adicQuotientIso [IsDomain A] [IsDiscreteValuationRing A]
    (hπ : Irreducible π) [IsProper f] [IsLocallyNoetherian X] {E G : X.Modules} [E.IsCoherent]
    [G.IsCoherent] {k e n : ℕ} (hE : StalkTorsionBounded E (baseScalarMap f π) k)
    (hG : StalkTorsionBounded G (baseScalarMap f π) k) (hn : k + (e + 1) ≤ n)
    (φ : adicQuotient f (Ideal.span {π}) n E ≅ adicQuotient f (Ideal.span {π}) n G)
    (hrank : Module.finrank A (cohomologyOver A f 0
          (adicFiltration f (Ideal.span {π}) k E).toSheafOfModules ⧸
        Submodule.torsion A (cohomologyOver A f 0
          (adicFiltration f (Ideal.span {π}) k E).toSheafOfModules)) =
      Module.finrank A (cohomologyOver A f 0
          (adicFiltration f (Ideal.span {π}) k G).toSheafOfModules ⧸
        Submodule.torsion A (cohomologyOver A f 0
          (adicFiltration f (Ideal.span {π}) k G).toSheafOfModules)))
    (hG₁ : Ideal.span {π} ^ e • Submodule.torsionBy A (cohomologyOver A f 1
      (adicFiltration f (Ideal.span {π}) k G).toSheafOfModules) (π ^ (e + 1)) = ⊥) :
    Ideal.span {π} ^ e • Submodule.torsionBy A (cohomologyOver A f 1
      (adicFiltration f (Ideal.span {π}) k E).toSheafOfModules) (π ^ (e + 1)) = ⊥ := by
  have : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have := isCoherent_adicFiltration A f π E k
  have := isCoherent_adicFiltration A f π G k
  have := moduleFinite_cohomologyOver A f
    ((adicFiltration f (Ideal.span {π}) k E).toSheafOfModules : X.Modules) 0
  have := moduleFinite_cohomologyOver A f
    ((adicFiltration f (Ideal.span {π}) k E).toSheafOfModules : X.Modules) 1
  have := moduleFinite_cohomologyOver A f
    ((adicFiltration f (Ideal.span {π}) k G).toSheafOfModules : X.Modules) 0
  have := moduleFinite_cohomologyOver A f
    ((adicFiltration f (Ideal.span {π}) k G).toSheafOfModules : X.Modules) 1
  have hG₀ : Ideal.span {π} ^ e • Submodule.torsionBy A (cohomologyOver A f 0
      (adicFiltration f (Ideal.span {π}) k G).toSheafOfModules) (π ^ (e + 1)) = ⊥ := by
    have hinj := injective_cohomology_adicReduction A f π G hG (e + 1)
    have hbot : Submodule.torsionBy A (cohomologyOver A f 0
        (adicFiltration f (Ideal.span {π}) k G).toSheafOfModules) (π ^ (e + 1)) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [Submodule.mem_torsionBy_iff] at hx
      refine (Submodule.mem_bot A).2 (hinj ((LinearMap.congr_fun
        (cohomologyMap_globalSmul A f 0 π (e + 1)
          ((adicFiltration f (Ideal.span {π}) k G).toSheafOfModules : X.Modules)) x).trans
        (hx.trans (map_zero _).symm)))
    rw [hbot, Submodule.smul_bot]
  refine pow_smul_torsionBy_eq_bot_of_length_eq hπ (m := e + 1) (by omega) hG₀ hG₁ hrank
    fun j hj₁ hj₂ => ?_
  rw [torsionLength, torsionLength, ← length_cohomology_adicImage A f π E hE j,
    ← length_cohomology_adicImage A f π G hG j]
  exact (cohomologyLinearEquiv 0 (adicImageIso (adicQuotientIsoOfLE (by omega) φ))).length_eq

end Stacks.AlgebraicGeometry.FreenessOverDVR
