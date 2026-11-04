module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicCompletionLimitComparison
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra

/-!
# The tower of cohomologies of the infinitesimal neighbourhoods

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` a quasi-coherent `𝒪_X`-module and `y` a point of
`Y`. Write `A = 𝒪_{Y, y}`, `𝔪 = 𝔪_y`, `X' = X ×_Y Spec A` with its projections
`g' : X' ⟶ X` and `f' : X' ⟶ Spec A`, `ℱ' = (g')^* ℱ` and `𝓘 = 𝔪 · 𝒪_{X'}`. The `n`-th
infinitesimal neighbourhood `X_n` of the fibre is the closed subscheme of `X'` cut out by
`𝓘 ⁿ` (`Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme`), so by [Stacks, Tag
0EL1] the quotient `ℱ' / 𝓘 ⁿ ℱ'` is the direct image of `ℱ_n = i_n ^* ℱ` along the closed
immersion `i_n : X_n ⟶ X'`, and because cohomology does not change along a closed immersion
([Stacks, Tag 01EX] and [Stacks, Tag 015M], as
`Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`) this gives

`H ᵖ (X', ℱ' / 𝓘 ⁿ ℱ') ≅ H ᵖ (X_n, ℱ_n)`

in every degree. This file builds that identification together with its compatibility with the
transition maps of the two towers, which is what turns the affine theorem on formal functions
over `Spec A` into a statement about the infinitesimal neighbourhoods of the fibre.

## Main definitions

* `Stacks.FormalFunctions.infinitesimalPushforwardIso` — **[Stacks, Tag 0EL1] for the
  infinitesimal neighbourhoods**: `ℱ' / 𝓘 ⁿ ℱ' ≅ (i_n)_* ℱ_n`.
* `Stacks.FormalFunctions.infinitesimalPushforwardDrop` — the canonical morphism
  `(i_n)_* ℱ_n ⟶ (i_m)_* ℱ_m` for `m ≤ n`, the direct image to `X'` of the restriction of
  sections from `X_n` to the smaller `X_m`.
* `Stacks.FormalFunctions.infinitesimalCohomology` — `H ᵖ (X_n, ℱ_n)`, as a module over `A` and
  over the completion `A ^∧_𝔪`.
* `Stacks.FormalFunctions.infinitesimalCohomologyMap` — **the transition map**
  `H ᵖ (X_n, ℱ_n) ⟶ H ᵖ (X_m, ℱ_m)` for `m ≤ n`.
* `Stacks.FormalFunctions.infinitesimalCompletedRingHom` — the ring map
  `A ^∧_𝔪 ⟶ Γ(X_n, 𝒪)`, through which the completed local ring acts on everything on `X_n`.
* `Stacks.FormalFunctions.restrictHomLinear`, `Stacks.FormalFunctions.restrictIsoLinear` and
  `Stacks.FormalFunctions.linearOfRepresentative` — the three changes of scalars, stated for
  abstract modules. They are what keeps the objects below out of every unification problem:
  the derived-functor objects in play are expensive to unfold, so each comparison of two
  module structures on one of them is made once, abstractly, and then instantiated.

## Main results

* `Stacks.FormalFunctions.ker_infinitesimalιBaseChange` — the ideal sheaf of `i_n : X_n ⟶ X'`
  is `𝓘 ⁿ`.
* `Stacks.FormalFunctions.appTop_infinitesimalιBaseChange_baseRingHom` — the two routes
  `A ⟶ Γ(X_n, 𝒪)`, through `Γ(X', 𝒪)` and through `𝒪_{Y, y}/𝔪 ⁿ`, agree.
* `Stacks.FormalFunctions.pow_smul_top_infinitesimalCohomology_eq_bot` — `𝔪 ⁿ` annihilates
  `H ᵖ (X_n, ℱ_n)`, which is what makes the completed local ring act on it.
* `Stacks.FormalFunctions.infinitesimalCohomologyEquiv` and
  `Stacks.FormalFunctions.infinitesimalCohomologyEquiv_naturality` — **the identification of the
  two towers**, `H ᵖ (X', ℱ' / 𝓘 ⁿ ℱ') ≅ H ᵖ (X_n, ℱ_n)`, compatible with the transitions.

## Implementation notes

**What the transition maps are.** The transition `H ᵖ (X_n, ℱ_n) ⟶ H ᵖ (X_m, ℱ_m)` is defined
through `X'`: it is `H ᵖ (X', −)` of the canonical morphism
`infinitesimalPushforwardDrop : (i_n)_* ℱ_n ⟶ (i_m)_* ℱ_m` of sheaves on `X'`, read through the
closed-immersion comparison. That morphism is pinned down by
`infinitesimalRestriction_comp_drop`: it is the unique morphism carrying the canonical
restriction `ℱ' ⟶ (i_n)_* ℱ_n` to the canonical restriction `ℱ' ⟶ (i_m)_* ℱ_m`, the latter being
an epimorphism. The equality of this map with the closed-immersion comparison taken along
`X_m ⟶ X_n` itself is **not** proved: that would need the compatibility of
`Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso` with a composition of closed
immersions, which this library does not have.

**Two rings act on `H ᵖ (X_n, ℱ_n)`.** The local ring `A` acts through
`Stacks.FormalFunctions.infinitesimalBaseRingHom`, and the completion `A ^∧_𝔪` acts through
`infinitesimalCompletedRingHom`, which is the evaluation `A ^∧_𝔪 ⟶ A/𝔪 ⁿ` followed by the same
structure morphism. The second action restricts to the first along `A ⟶ A ^∧_𝔪`, which is the
scalar-tower instance below; and because the two differ only by a choice of representative in
`A` of a class in `A/𝔪 ⁿ`, every `A`-linear map between two such modules is automatically
`A ^∧_𝔪`-linear. That is what `infinitesimalCohomologyMap` uses to be linear over the completion
although it is built from a `Γ(X', 𝒪)`-linear map.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.FormalFunctions

open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

/-- **Restriction of scalars does not change the action**: a scalar of `R` acts on the
restricted module through the ring map. Stated for an abstract module so that it can be applied
to one whose underlying object is expensive to unfold. -/
public theorem restrictScalars_smul_eq {R S : Type*} [Ring R] [Ring S] (σ : R →+* S)
    (M : ModuleCat.{u} S) (r : R) (x : M) :
    (r • (show (ModuleCat.restrictScalars σ).obj M from x) : (ModuleCat.restrictScalars σ).obj M)
      = σ r • x :=
  rfl

/-- **A morphism between two restrictions of scalars, read as a linear map over a third ring.**
If `A` acts on the two sides through ring maps `α : A ⟶ S` and `β : A ⟶ T` which are the
composites of a single `ρ : A ⟶ R` with the two restricting maps, then a morphism of
`R`-modules between the restrictions is `A`-linear. Everything here is abstract, so that it can
be instantiated at modules whose underlying objects are expensive to unfold. -/
public def restrictHomLinear {A R S T : Type*} [CommRing A] [CommRing R] [CommRing S]
    [CommRing T] (σ : R →+* S) (τ : R →+* T) {M : ModuleCat.{u} S} {N : ModuleCat.{u} T}
    (φ : (ModuleCat.restrictScalars σ).obj M ⟶ (ModuleCat.restrictScalars τ).obj N)
    (α : A →+* S) (β : A →+* T) (ρ : A →+* R)
    (hα : ∀ a, σ (ρ a) = α a) (hβ : ∀ a, τ (ρ a) = β a) :
    letI := Module.compHom (M : Type u) α
    letI := Module.compHom (N : Type u) β
    (M : Type u) →ₗ[A] (N : Type u) :=
  letI := Module.compHom (M : Type u) α
  letI := Module.compHom (N : Type u) β
  { toFun := φ.hom
    map_add' := map_add φ.hom
    map_smul' := fun a x => by
      change φ.hom (α a • x) = β a • φ.hom x
      rw [← hα, ← hβ]
      exact φ.hom.map_smul (ρ a) x }

/-- `restrictHomLinear` acts on elements as the underlying morphism `φ`. -/
@[simp]
public theorem restrictHomLinear_apply {A R S T : Type*} [CommRing A] [CommRing R] [CommRing S]
    [CommRing T] (σ : R →+* S) (τ : R →+* T) {M : ModuleCat.{u} S} {N : ModuleCat.{u} T}
    (φ : (ModuleCat.restrictScalars σ).obj M ⟶ (ModuleCat.restrictScalars τ).obj N)
    (α : A →+* S) (β : A →+* T) (ρ : A →+* R)
    (hα : ∀ a, σ (ρ a) = α a) (hβ : ∀ a, τ (ρ a) = β a) (x : M) :
    letI := Module.compHom (M : Type u) α
    letI := Module.compHom (N : Type u) β
    restrictHomLinear σ τ φ α β ρ hα hβ x = φ.hom x :=
  rfl

/-- **An isomorphism onto a restriction of scalars, read as a linear equivalence over a third
ring.** The companion of `restrictHomLinear` for the comparison of the two towers. -/
public def restrictIsoLinear {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    (σ : R →+* S) {P : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (e : P ≅ (ModuleCat.restrictScalars σ).obj N) (β : A →+* S) (ρ : A →+* R)
    (hβ : ∀ a, σ (ρ a) = β a) :
    letI := Module.compHom (P : Type u) ρ
    letI := Module.compHom (N : Type u) β
    (P : Type u) ≃ₗ[A] (N : Type u) :=
  letI := Module.compHom (P : Type u) ρ
  letI := Module.compHom (N : Type u) β
  { toFun := e.hom.hom
    map_add' := map_add e.hom.hom
    map_smul' := fun a x => by
      change e.hom.hom (ρ a • x) = β a • e.hom.hom x
      rw [← hβ]
      exact e.hom.hom.map_smul (ρ a) x
    invFun := e.inv.hom
    left_inv := fun x => congrFun (congrArg (fun ψ => (ModuleCat.Hom.hom ψ : _ → _))
      e.hom_inv_id) x
    right_inv := fun x => congrFun (congrArg (fun ψ => (ModuleCat.Hom.hom ψ : _ → _))
      e.inv_hom_id) x }

/-- `restrictIsoLinear` acts on elements as the forward morphism of the isomorphism `e`. -/
@[simp]
public theorem restrictIsoLinear_apply {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    (σ : R →+* S) {P : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (e : P ≅ (ModuleCat.restrictScalars σ).obj N) (β : A →+* S) (ρ : A →+* R)
    (hβ : ∀ a, σ (ρ a) = β a) (x : P) :
    letI := Module.compHom (P : Type u) ρ
    letI := Module.compHom (N : Type u) β
    restrictIsoLinear σ e β ρ hβ x = e.hom.hom x :=
  rfl

/-- The square expressing that two comparisons `restrictIsoLinear` intertwine a map of the
sources with a `restrictHomLinear` of the targets, read on elements from the corresponding
identity of morphisms. -/
public theorem restrictIsoLinear_naturality {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] (σ : R →+* S) (τ : R →+* T) {P Q : ModuleCat.{u} R}
    {M : ModuleCat.{u} S} {N : ModuleCat.{u} T} (d : Q ⟶ P)
    (e : Q ≅ (ModuleCat.restrictScalars σ).obj M)
    (e' : P ≅ (ModuleCat.restrictScalars τ).obj N)
    (φ : (ModuleCat.restrictScalars σ).obj M ⟶ (ModuleCat.restrictScalars τ).obj N)
    (hsq : d ≫ e'.hom = e.hom ≫ φ) (x : Q) :
    e'.hom.hom (d.hom x) = φ.hom (e.hom.hom x) := by
  have key := ConcreteCategory.congr_hom hsq x
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using key

/-- **An `A`-linear map between modules over a larger ring `B` is `B`-linear** as soon as every
scalar of `B` acts on both sides as one and the same scalar of `A`. -/
public def linearOfRepresentative {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [Module B M] [AddCommGroup N] [Module A N] [Module B N]
    (φ : M →ₗ[A] N) (rep : B → A) (hM : ∀ (b : B) (x : M), b • x = rep b • x)
    (hN : ∀ (b : B) (x : N), b • x = rep b • x) : M →ₗ[B] N where
  toFun := φ
  map_add' := map_add φ
  map_smul' b x := by rw [RingHom.id_apply, hM, hN, map_smul]

/-- `linearOfRepresentative` acts on elements as the `A`-linear map `φ`. -/
@[simp]
public theorem linearOfRepresentative_apply {A B M N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [Module B M] [AddCommGroup N] [Module A N] [Module B N]
    (φ : M →ₗ[A] N) (rep : B → A) (hM : ∀ (b : B) (x : M), b • x = rep b • x)
    (hN : ∀ (b : B) (x : N), b • x = rep b • x) (x : M) :
    linearOfRepresentative φ rep hM hN x = φ x :=
  rfl

variable {X Y : Scheme.{u}}

/-! ### The ideal sheaf of `X_n` inside `X'` -/

/-- **The ideal sheaf of the closed immersion `i_n : X_n ⟶ X'` is `𝓘 ⁿ`.** The identification
`Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme` carries the inclusion of the
subscheme cut out by `𝓘 ⁿ` to `i_n`, and an isomorphism in front of a morphism does not change
its ideal sheaf. -/
public theorem ker_infinitesimalιBaseChange (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (infinitesimalιBaseChange f y n).ker = infinitesimalBaseIdealSheaf f y ^ n := by
  rw [← Scheme.Hom.ker_comp_of_isIso (infinitesimalNeighbourhoodIsoSubscheme f y n).hom
      (infinitesimalιBaseChange f y n),
    infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange,
    Scheme.IdealSheafData.ker_subschemeι]

/-! ### The two routes from the local ring to the functions on `X_n` -/

/-- **The two routes `𝒪_{Y, y} ⟶ Γ(X_n, 𝒪)` agree**: pulling a function back from `X'` and
restricting it to `X_n` is the same as pushing it through `𝒪_{Y, y}/𝔪_y ⁿ` and the structure
morphism `f_n`. Both are read off the defining square of `X_n` over `X'`. -/
public theorem appTop_infinitesimalιBaseChange_baseRingHom (f : X ⟶ Y) (y : Y) (n : ℕ)
    (a : Y.presheaf.stalk y) :
    (infinitesimalιBaseChange f y n).appTop.hom
        (baseRingHom (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) a) =
      infinitesimalBaseRingHom f y n a := by
  have key : (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv ≫
        (stalkBaseChangeStructure f y).appTop ≫ (infinitesimalιBaseChange f y n).appTop =
      toStalkQuotient y n ≫ (Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
        (infinitesimalStructure f y n).appTop := by
    rw [← Scheme.Hom.comp_appTop, infinitesimalιBaseChange_comp_structure,
      Scheme.Hom.comp_appTop,
      show (Spec.map (toStalkQuotient y n)).appTop = (Spec.map (toStalkQuotient y n)).appTop
        from rfl, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact ConcreteCategory.congr_hom key a


/-! ### The quotients of `ℱ'` as direct images from the infinitesimal neighbourhoods -/

variable (f : X ⟶ Y) (F : X.Modules) (y : Y)

/-- **`ℱ_n` is the restriction of `ℱ'` to `X_n`**, since `i_n : X_n ⟶ X` factors through
`X' = X ×_Y Spec 𝒪_{Y, y}`. -/
public def infinitesimalModulePullbackIso (n : ℕ) :
    (Scheme.Modules.pullback (infinitesimalιBaseChange f y n)).obj
        (stalkBaseChangeModule f F y) ≅ infinitesimalModule f F y n :=
  (Scheme.Modules.pullbackComp (infinitesimalιBaseChange f y n) (stalkBaseChangeι f y)).app F ≪≫
    (Scheme.Modules.pullbackCongr (infinitesimalιBaseChange_comp_ι f y n)).app F

/-- **[Stacks, Tag 0EL1] for the infinitesimal neighbourhoods of the fibre.** The quotient
`ℱ' / 𝓘 ⁿ ℱ'` on `X' = X ×_Y Spec 𝒪_{Y, y}` is the direct image of `ℱ_n` along the closed
immersion `i_n : X_n ⟶ X'`, whose ideal sheaf is `𝓘 ⁿ`. -/
public def infinitesimalPushforwardIso [F.IsQuasicoherent] (n : ℕ) :
    idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y) ≅
      (Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).obj
        (infinitesimalModule f F y n) :=
  idealQuotientPushforwardIso (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y)
      (infinitesimalιBaseChange f y n) (ker_infinitesimalιBaseChange f y n) ≪≫
    (Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).mapIso
      (infinitesimalModulePullbackIso f F y n)

/-- **The canonical morphism `(i_n)_* ℱ_n ⟶ (i_m)_* ℱ_m` for `m ≤ n`**, the direct image to `X'`
of the restriction of sections from `X_n` to the smaller neighbourhood `X_m`. It is read off the
exponent-lowering map `ℱ' / 𝓘 ⁿ ℱ' ⟶ ℱ' / 𝓘 ᵐ ℱ'`. -/
public def infinitesimalPushforwardDrop [F.IsQuasicoherent] {m n : ℕ} (h : m ≤ n) :
    (Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).obj
        (infinitesimalModule f F y n) ⟶
      (Scheme.Modules.pushforward (infinitesimalιBaseChange f y m)).obj
        (infinitesimalModule f F y m) :=
  (infinitesimalPushforwardIso f F y n).inv ≫
    idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h (stalkBaseChangeModule f F y) ≫
    (infinitesimalPushforwardIso f F y m).hom

/-- **The canonical restriction `ℱ' ⟶ (i_n)_* ℱ_n`**, the quotient projection read through
[Stacks, Tag 0EL1]. -/
public def infinitesimalRestriction [F.IsQuasicoherent] (n : ℕ) :
    stalkBaseChangeModule f F y ⟶
      (Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).obj
        (infinitesimalModule f F y n) :=
  cokernel.π (C := (stalkBaseChange f y).Modules)
      (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
        (stalkBaseChangeModule f F y)).ι ≫
    (infinitesimalPushforwardIso f F y n).hom

/-- **The transition morphism is the one compatible with the canonical restrictions**:
restricting `ℱ'` to `X_n` and then to `X_m` is restricting it to `X_m`. Since the canonical
restriction is an epimorphism, this determines `infinitesimalPushforwardDrop`. -/
public theorem infinitesimalRestriction_comp_drop [F.IsQuasicoherent] {m n : ℕ} (h : m ≤ n) :
    infinitesimalRestriction f F y n ≫ infinitesimalPushforwardDrop f F y h =
      infinitesimalRestriction f F y m := by
  rw [infinitesimalRestriction, infinitesimalRestriction, infinitesimalPushforwardDrop,
    Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
    idealPowerQuotientDrop_π]

/-! ### The cohomology of the infinitesimal neighbourhoods, as a tower of modules -/

/-- **`H ᵖ (X_n, ℱ_n)`**, the cohomology of the restriction of `ℱ` to the `n`-th infinitesimal
neighbourhood of the fibre of `f` over `y`. -/
public abbrev infinitesimalCohomology (p n : ℕ) : Type u :=
  ((Stacks.Cohomology.AffineBase.moduleGlobalSections
    (infinitesimalNeighbourhood f y n)).rightDerived p).obj (infinitesimalModule f F y n)

/-- The local ring `𝒪_{Y, y}` acts on `H ᵖ (X_n, ℱ_n)` through
`Stacks.FormalFunctions.infinitesimalBaseRingHom`. -/
public instance (priority := 100) moduleInfinitesimalCohomology (p n : ℕ) :
    Module (Y.presheaf.stalk y) (infinitesimalCohomology f F y p n) :=
  Module.compHom _ (infinitesimalBaseRingHom f y n)

/-- A scalar of `𝒪_{Y, y}` acts on `H ᵖ (X_n, ℱ_n)` as its image under
`Stacks.FormalFunctions.infinitesimalBaseRingHom`. -/
public theorem infinitesimalCohomology_smul_def (p n : ℕ) (r : Y.presheaf.stalk y)
    (x : infinitesimalCohomology f F y p n) :
    r • x = infinitesimalBaseRingHom f y n r • x :=
  rfl

/-- **The ring map `𝒪 ^∧_{Y, y} ⟶ Γ(X_n, 𝒪)`.** The completed local ring acts on everything on
`X_n` through its truncation `𝒪_{Y, y}/𝔪_y ⁿ` and the structure morphism `f_n`. -/
public def infinitesimalCompletedRingHom (n : ℕ) :
    AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y) →+*
      Γ(infinitesimalNeighbourhood f y n, ⊤) :=
  RingHom.comp
    (((Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
      (infinitesimalStructure f y n).appTop).hom)
    (AdicCompletion.evalₐ (stalkMaximalIdeal y) n).toRingHom

/-- **The completed local ring and the local ring act compatibly**: a scalar of `𝒪 ^∧_{Y, y}`
acts as any element of `𝒪_{Y, y}` representing its class modulo `𝔪_y ⁿ`. -/
public theorem infinitesimalCompletedRingHom_eq_of_evalₐ (n : ℕ)
    (r : AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
    (a : Y.presheaf.stalk y)
    (ha : AdicCompletion.evalₐ (stalkMaximalIdeal y) n r =
      Ideal.Quotient.mk (stalkMaximalIdeal y ^ n) a) :
    infinitesimalCompletedRingHom f y n r = infinitesimalBaseRingHom f y n a := by
  show (((Scheme.ΓSpecIso (stalkQuotient y n)).inv ≫
      (infinitesimalStructure f y n).appTop).hom)
    (AdicCompletion.evalₐ (stalkMaximalIdeal y) n r) = _
  rw [ha]
  rfl

/-- The completed local ring `𝒪 ^∧_{Y, y}` acts on `H ᵖ (X_n, ℱ_n)` through
`infinitesimalCompletedRingHom`. -/
public instance (priority := 100) moduleCompletedInfinitesimalCohomology (p n : ℕ) :
    Module (AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
      (infinitesimalCohomology f F y p n) :=
  Module.compHom _ (infinitesimalCompletedRingHom f y n)

/-- A scalar of `𝒪 ^∧_{Y, y}` acts on `H ᵖ (X_n, ℱ_n)` as its image under
`infinitesimalCompletedRingHom`. -/
public theorem infinitesimalCohomology_completed_smul_def (p n : ℕ)
    (r : AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
    (x : infinitesimalCohomology f F y p n) :
    r • x = infinitesimalCompletedRingHom f y n r • x :=
  rfl

/-- **A scalar of the completion acts as any of its representatives in the local ring.** -/
public theorem infinitesimalCohomology_smul_eq (p n : ℕ)
    (r : AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
    (a : Y.presheaf.stalk y)
    (ha : AdicCompletion.evalₐ (stalkMaximalIdeal y) n r =
      Ideal.Quotient.mk (stalkMaximalIdeal y ^ n) a)
    (x : infinitesimalCohomology f F y p n) : r • x = a • x := by
  rw [infinitesimalCohomology_completed_smul_def, infinitesimalCohomology_smul_def,
    infinitesimalCompletedRingHom_eq_of_evalₐ f y n r a ha]

/-- The actions of `𝒪_{Y, y}` and of `𝒪 ^∧_{Y, y}` on `H ᵖ (X_n, ℱ_n)` form a scalar tower. -/
public instance isScalarTowerInfinitesimalCohomology (p n : ℕ) :
    IsScalarTower (Y.presheaf.stalk y)
      (AdicCompletion (stalkMaximalIdeal y) (Y.presheaf.stalk y))
      (infinitesimalCohomology f F y p n) := by
  refine ⟨fun a r x => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (stalkMaximalIdeal y) n r)
  rw [infinitesimalCohomology_smul_eq f F y p n r b hb.symm,
    infinitesimalCohomology_smul_eq f F y p n (a • r) (a * b) ?_, mul_smul]
  rw [map_smul, ← hb, Algebra.smul_def, map_mul, Ideal.Quotient.algebraMap_eq]

/-- **`𝔪_y ⁿ` annihilates `H ᵖ (X_n, ℱ_n)`**: it is already killed by the ring map through which
the local ring acts. -/
public theorem pow_smul_top_infinitesimalCohomology_eq_bot (p n : ℕ) :
    stalkMaximalIdeal y ^ n •
        (⊤ : Submodule (Y.presheaf.stalk y) (infinitesimalCohomology f F y p n)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.2 fun r hr x _ => ?_) bot_le
  rw [Submodule.mem_bot, infinitesimalCohomology_smul_def,
    infinitesimalBaseRingHom_eq_zero f y n hr, zero_smul]

/-! ### The transition maps -/

/-- The transition in cohomology, as a morphism of `Γ(X', 𝒪)`-modules: `H ᵖ (X', −)` of the
canonical morphism `(i_n)_* ℱ_n ⟶ (i_m)_* ℱ_m`, read through the closed-immersion
comparison. -/
public def infinitesimalCohomologyHom [F.IsQuasicoherent] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    (ModuleCat.restrictScalars (infinitesimalιBaseChange f y n).appTop.hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (infinitesimalNeighbourhood f y n)).rightDerived p).obj
            (infinitesimalModule f F y n)) ⟶
      (ModuleCat.restrictScalars (infinitesimalιBaseChange f y m).appTop.hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (infinitesimalNeighbourhood f y m)).rightDerived p).obj
            (infinitesimalModule f F y m)) :=
  (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward
      (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n) p).inv ≫
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (stalkBaseChange f y)).rightDerived p).map (infinitesimalPushforwardDrop f F y h) ≫
    (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward
      (infinitesimalιBaseChange f y m) (infinitesimalModule f F y m) p).hom

/-- **The transition map `H ᵖ (X_n, ℱ_n) ⟶ H ᵖ (X_m, ℱ_m)` for `m ≤ n`**, linear over the local
ring: the actions of `𝒪_{Y, y}` on the two sides are both induced by its action on the
functions on `X'`. -/
public def infinitesimalCohomologyMapStalk [F.IsQuasicoherent] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    infinitesimalCohomology f F y p n →ₗ[Y.presheaf.stalk y]
      infinitesimalCohomology f F y p m :=
  restrictHomLinear (infinitesimalιBaseChange f y n).appTop.hom
    (infinitesimalιBaseChange f y m).appTop.hom (infinitesimalCohomologyHom f F y p h)
    (infinitesimalBaseRingHom f y n) (infinitesimalBaseRingHom f y m)
    (baseRingHom (Y.presheaf.stalk y) (stalkBaseChangeStructure f y))
    (appTop_infinitesimalιBaseChange_baseRingHom f y n)
    (appTop_infinitesimalιBaseChange_baseRingHom f y m)

/-- **The transition map, linear over the completed local ring.** A scalar of the completion
acts through a representative in the local ring, and because the truncations are compatible the
same representative serves at both levels. -/
public def infinitesimalCohomologyMap [F.IsQuasicoherent] (p : ℕ) (m n : ℕ) (h : m ≤ n) :
    infinitesimalCohomology f F y p n →ₗ[AdicCompletion (stalkMaximalIdeal y)
        (Y.presheaf.stalk y)] infinitesimalCohomology f F y p m :=
  linearOfRepresentative (infinitesimalCohomologyMapStalk f F y p h)
    (fun r => (Stacks.AdicCompletion.PrimesOverProduct.exists_evalₐ_eq_mk
      (stalkMaximalIdeal y) h r).choose)
    (fun r x => infinitesimalCohomology_smul_eq f F y p n r _
      (Stacks.AdicCompletion.PrimesOverProduct.exists_evalₐ_eq_mk
        (stalkMaximalIdeal y) h r).choose_spec.1 x)
    (fun r x => infinitesimalCohomology_smul_eq f F y p m r _
      (Stacks.AdicCompletion.PrimesOverProduct.exists_evalₐ_eq_mk
        (stalkMaximalIdeal y) h r).choose_spec.2 x)

/-! ### The identification of the two towers -/

/-- The comparison `H ᵖ (X', ℱ' / 𝓘 ⁿ ℱ') ≅ H ᵖ (X_n, ℱ_n)` at the level of
`Γ(X', 𝒪)`-modules. -/
public def infinitesimalCohomologyIso [F.IsQuasicoherent] (p n : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (stalkBaseChange f y)).rightDerived p).obj
        (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n
          (stalkBaseChangeModule f F y)) ≅
      (ModuleCat.restrictScalars (infinitesimalιBaseChange f y n).appTop.hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (infinitesimalNeighbourhood f y n)).rightDerived p).obj
            (infinitesimalModule f F y n)) :=
  ((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (stalkBaseChange f y)).rightDerived p).mapIso (infinitesimalPushforwardIso f F y n) ≪≫
    Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward
      (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n) p

/-- **The comparison is compatible with the transitions of the two towers.** -/
public theorem infinitesimalCohomologyIso_naturality [F.IsQuasicoherent] (p : ℕ) {m n : ℕ}
    (h : m ≤ n) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (stalkBaseChange f y)).rightDerived p).map
        (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (stalkBaseChangeModule f F y)) ≫ (infinitesimalCohomologyIso f F y p m).hom =
      (infinitesimalCohomologyIso f F y p n).hom ≫ infinitesimalCohomologyHom f F y p h := by
  have hp : (infinitesimalPushforwardIso f F y n).hom ≫ infinitesimalPushforwardDrop f F y h =
      idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (stalkBaseChangeModule f F y) ≫ (infinitesimalPushforwardIso f F y m).hom := by
    rw [infinitesimalPushforwardDrop, Iso.hom_inv_id_assoc]
  simp only [infinitesimalCohomologyIso, infinitesimalCohomologyHom, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hp]

/-- **The comparison of the two towers, as an isomorphism of `𝒪_{Y, y}`-modules**:
`H ᵖ (X', ℱ' / 𝓘 ⁿ ℱ') ≅ H ᵖ (X_n, ℱ_n)`. -/
public def infinitesimalCohomologyEquiv [F.IsQuasicoherent] (p n : ℕ) :
    cohomologyOverBase (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
        (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n
          (stalkBaseChangeModule f F y)) ≃ₗ[Y.presheaf.stalk y]
      infinitesimalCohomology f F y p n :=
  restrictIsoLinear (infinitesimalιBaseChange f y n).appTop.hom
    (infinitesimalCohomologyIso f F y p n) (infinitesimalBaseRingHom f y n)
    (baseRingHom (Y.presheaf.stalk y) (stalkBaseChangeStructure f y))
    (appTop_infinitesimalιBaseChange_baseRingHom f y n)

/-- `infinitesimalCohomologyMap` acts on elements as the transition morphism
`infinitesimalCohomologyHom`. -/
@[simp]
public theorem infinitesimalCohomologyMap_apply [F.IsQuasicoherent] (p : ℕ) (m n : ℕ)
    (h : m ≤ n) (x : infinitesimalCohomology f F y p n) :
    infinitesimalCohomologyMap f F y p m n h x =
      (infinitesimalCohomologyHom f F y p h).hom x :=
  rfl

/-- `infinitesimalCohomologyEquiv` acts on elements as the forward morphism of
`infinitesimalCohomologyIso`. -/
@[simp]
public theorem infinitesimalCohomologyEquiv_apply [F.IsQuasicoherent] (p n : ℕ)
    (x : cohomologyOverBase (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
      (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y))) :
    infinitesimalCohomologyEquiv f F y p n x =
      (infinitesimalCohomologyIso f F y p n).hom.hom x :=
  rfl

/-- The transition of the affine tower, read on elements. -/
public theorem cohomologyOverBaseMap_apply_eq [F.IsQuasicoherent] (p : ℕ) {m n : ℕ} (h : m ≤ n)
    (x : cohomologyOverBase (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
      (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y))) :
    (cohomologyOverBaseMap (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
        (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (stalkBaseChangeModule f F y))).hom x =
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (stalkBaseChange f y)).rightDerived p).map
        (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (stalkBaseChangeModule f F y))).hom x :=
  rfl

/-- **The comparison of the two towers commutes with the transition maps.** -/
public theorem infinitesimalCohomologyEquiv_naturality [F.IsQuasicoherent] (p : ℕ) (m n : ℕ)
    (h : m ≤ n)
    (x : cohomologyOverBase (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
      (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y))) :
    infinitesimalCohomologyEquiv f F y p m
        ((cohomologyOverBaseMap (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) p
          (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
            (stalkBaseChangeModule f F y))).hom x) =
      (infinitesimalCohomologyMap f F y p m n h).restrictScalars (Y.presheaf.stalk y)
        (infinitesimalCohomologyEquiv f F y p n x) := by
  simp only [cohomologyOverBaseMap_apply_eq, infinitesimalCohomologyEquiv_apply]
  exact restrictIsoLinear_naturality _ _ _ _ _ _
    (infinitesimalCohomologyIso_naturality f F y p h) x

end Stacks.FormalFunctions

end
