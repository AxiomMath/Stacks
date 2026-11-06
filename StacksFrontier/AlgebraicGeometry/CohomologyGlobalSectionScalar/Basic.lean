module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.Homology.DerivedLinear

/-!
# A global function acts on cohomology as a scalar

Let `X` be a scheme over a field `k` and let `a` be a global section of `𝒪_X`.  Multiplication
by `a` is an endomorphism `𝒪_X`-linear in every sheaf of modules and natural in it, so it induces
an endomorphism of `Hᵖ(X, ℱ)`.  This file identifies that endomorphism: it is multiplication by
`a` for the `Γ(X, ⊤)`-module structure that `Hᵖ(X, ℱ)` carries, hence — when `a` is the image of
`c ∈ k` under the structure morphism — multiplication by `c` on
`AlgebraicGeometry.cohomologyOverField`.

The content is that the category of `𝒪_X`-modules and the category of `Γ(X, ⊤)`-modules are
both `Γ(X, ⊤)`-linear, that global sections is a `Γ(X, ⊤)`-linear functor, and that the right
derived functors of a linear functor are linear
(`Stacks.DerivedLinear.rightDerived_linear`).

## Main results

* `AlgebraicGeometry.globalSmul`: multiplication of a sheaf of modules by a global function.
* `AlgebraicGeometry.linearModules`: the category of `𝒪_X`-modules is `Γ(X, ⊤)`-linear.
* `AlgebraicGeometry.cohomologyOverFieldMap_globalSmul`: **the map induced on cohomology by
  multiplication by the image of `c ∈ k` is multiplication by `c`.**
* `AlgebraicGeometry.terminal_opens_eq_top`: the terminal open of a scheme is the whole space.

## Implementation notes

`AlgebraicGeometry.globalSmul` is `Stacks.SheafOfModules.globalSectionToEnd` applied to the
compatible family of restrictions of `a`.  The family is written out rather than obtained from
`Stacks.SheafOfModules.terminalSection`, because the terminal object `⊤_ (Opens X)` of the site
is not definitionally `(⊤ : X.Opens)`, while `AlgebraicGeometry.cohomologyOverField`
is stated at `⊤`.  Compatibility of the family is functoriality of the structure presheaf
together with the fact that `Opens X` is a partial order, so that the two restriction maps in
play are equal because the morphisms are.

`AlgebraicGeometry.cohomologyOverFieldMap` is `@[irreducible]`, so the last step unfolds it with
`with_unfolding_all`, as `AlgebraicGeometry.cohomologyOverFieldZeroLinearIso_naturality` does.

The commutativity of the rings of sections that `Stacks.SheafOfModules.globalSectionToEnd` asks
for is `AlgebraicGeometry.Scheme.isMulCommutative_ringCatSheaf`.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The restriction of a global function to an open. -/
def restrictTop (a : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a

/-- The compatible family of restrictions of a global function to all opens. -/
def globalRestrictFamily (a : Γ(X, ⊤)) :
    (X.ringCatSheaf.obj ⋙ forget RingCat).sections where
  val U := restrictTop a U.unop
  property {U V} i := by
    have h : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ i = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
      Subsingleton.elim _ _
    change (X.presheaf.map i) (restrictTop a U.unop) = restrictTop a V.unop
    unfold restrictTop
    conv_rhs => rw [← h, X.presheaf.map_comp]
    rfl

/-- Restricting a global function to the whole space gives it back. -/
theorem restrictTop_top (a : Γ(X, ⊤)) : restrictTop a (⊤ : X.Opens) = a := by
  simp [restrictTop]

/-- **Multiplication of a sheaf of modules by a global function.** -/
def globalSmul (a : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  (Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf (globalRestrictFamily a)).asHom.app M

/-- On sections over `U`, `globalSmul a M` is multiplication by the restriction of `a` to `U`. -/
theorem globalSmul_app (a : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (globalSmul a M).app U x = restrictTop a U • x :=
  Stacks.SheafOfModules.globalSectionToEnd_apply X.ringCatSheaf (globalRestrictFamily a) M
    (op U) x

/-- On global sections, `globalSmul a M` is multiplication by `a`. -/
theorem globalSmul_app_top (a : Γ(X, ⊤)) (M : X.Modules) (x : Γ(M, ⊤)) :
    (globalSmul a M).app ⊤ x = a • x := by
  rw [globalSmul_app, restrictTop_top]

/-- Multiplication by a global function is natural in the sheaf of modules. -/
theorem comp_globalSmul (a : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    φ ≫ globalSmul a N = globalSmul a M ≫ φ :=
  (Stacks.SheafOfModules.globalSectionToEnd X.ringCatSheaf
    (globalRestrictFamily a)).asHom.naturality φ

/-- Multiplication by `1` is the identity. -/
theorem globalSmul_one (M : X.Modules) : globalSmul (1 : Γ(X, ⊤)) M = 𝟙 M := by
  ext U x
  rw [globalSmul_app, show restrictTop (1 : Γ(X, ⊤)) U = 1 from map_one _, one_smul]
  rfl

/-- Multiplication by `a * b` is multiplication by `a` followed by multiplication by `b`. -/
theorem globalSmul_mul (a b : Γ(X, ⊤)) (M : X.Modules) :
    globalSmul (a * b) M = globalSmul a M ≫ globalSmul b M := by
  ext U x
  change _ = (globalSmul b M).app U ((globalSmul a M).app U x)
  rw [globalSmul_app, globalSmul_app, globalSmul_app,
    show restrictTop (a * b) U = restrictTop a U * restrictTop b U from map_mul _ _ _,
    mul_comm, mul_smul]

/-- Multiplication by a global function is additive in the function. -/
theorem globalSmul_add (a b : Γ(X, ⊤)) (M : X.Modules) :
    globalSmul (a + b) M = globalSmul a M + globalSmul b M := by
  ext U x
  rw [globalSmul_app,
    show restrictTop (a + b) U = restrictTop a U + restrictTop b U from map_add _ _ _, add_smul]
  rfl

/-- Multiplication by `0` is the zero morphism. -/
theorem globalSmul_zero (M : X.Modules) : globalSmul (0 : Γ(X, ⊤)) M = 0 := by
  ext U x
  rw [globalSmul_app, show restrictTop (0 : Γ(X, ⊤)) U = 0 from map_zero _, zero_smul]
  rfl

/-- Morphisms of `𝒪_X`-modules are a module over the ring of global functions. -/
instance homModule (M N : X.Modules) : Module ↥Γ(X, ⊤) (M ⟶ N) where
  smul a φ := globalSmul a M ≫ φ
  one_smul φ := by
    change globalSmul (1 : Γ(X, ⊤)) M ≫ φ = φ
    rw [globalSmul_one, Category.id_comp]
  mul_smul a b φ := by
    change globalSmul (a * b) M ≫ φ = globalSmul a M ≫ globalSmul b M ≫ φ
    rw [globalSmul_mul, Category.assoc]
  smul_zero a := by
    change globalSmul a M ≫ (0 : M ⟶ N) = 0
    simp
  smul_add a φ ψ := by
    change globalSmul a M ≫ (φ + ψ) = globalSmul a M ≫ φ + globalSmul a M ≫ ψ
    simp
  add_smul a b φ := by
    change globalSmul (a + b) M ≫ φ = globalSmul a M ≫ φ + globalSmul b M ≫ φ
    rw [globalSmul_add, Preadditive.add_comp]
  zero_smul φ := by
    change globalSmul (0 : Γ(X, ⊤)) M ≫ φ = 0
    rw [globalSmul_zero, Limits.zero_comp]

/-- The scalar `a • φ` is `φ` precomposed with multiplication by `a`. -/
theorem smul_hom_def (a : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    a • φ = globalSmul a M ≫ φ := rfl

/-- **The category of `𝒪_X`-modules is `Γ(X, ⊤)`-linear.** -/
instance linearModules : Linear ↥Γ(X, ⊤) X.Modules where
  smul_comp M N P a φ ψ := by
    change (globalSmul a M ≫ φ) ≫ ψ = globalSmul a M ≫ φ ≫ ψ
    rw [Category.assoc]
  comp_smul M N P φ a ψ := by
    change φ ≫ globalSmul a N ≫ ψ = globalSmul a M ≫ φ ≫ ψ
    rw [← Category.assoc, comp_globalSmul, Category.assoc]

/-- Multiplication by `a` is the scalar multiple `a • 𝟙 M` of the identity. -/
theorem globalSmul_eq_smul_id (a : Γ(X, ⊤)) (M : X.Modules) : globalSmul a M = a • 𝟙 M := by
  rw [smul_hom_def, Category.comp_id]

/-- **Global sections is a `Γ(X, ⊤)`-linear functor.** -/
instance moduleGlobalSections_linear (X : Scheme.{u}) :
    Functor.Linear ↥Γ(X, ⊤) (moduleGlobalSections X) where
  map_smul {M N} φ a := by
    change (moduleGlobalSections X).map (globalSmul a M ≫ φ) = _
    rw [Functor.map_comp]
    have h : (moduleGlobalSections X).map (globalSmul a M) = a • 𝟙 _ := by
      ext x
      exact globalSmul_app_top a M x
    rw [h, Linear.smul_comp, Category.id_comp]

/-- **The right derived functors of global sections are `Γ(X, ⊤)`-linear.** -/
instance rightDerived_moduleGlobalSections_linear (X : Scheme.{u}) (p : ℕ) :
    Functor.Linear ↥Γ(X, ⊤) ((moduleGlobalSections X).rightDerived p) :=
  Stacks.DerivedLinear.rightDerived_linear _ p

/-! ### The terminal open -/

/-- **The terminal object of the category of opens of a scheme is the whole space.** -/
theorem terminal_opens_eq_top (X : Scheme.{u}) : (⊤_ (Opens X)) = (⊤ : X.Opens) :=
  le_antisymm le_top (leOfHom (terminal.from (⊤ : X.Opens)))

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The image in `Γ(X, ⊤)` of a scalar `c ∈ k` under the ring map induced by the structure
morphism `f : X ⟶ Spec k`: the ring map through which `AlgebraicGeometry.cohomologyOverField`
restricts scalars. -/
def baseScalarSection (c : k) : Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c

/-- **Multiplication by the image of `c ∈ k` induces multiplication by `c` on cohomology.** -/
theorem cohomologyOverFieldMap_globalSmul (c : k) (M : X.Modules) (p : ℕ)
    (z : cohomologyOverField k f M p) :
    cohomologyOverFieldMap k f (globalSmul (baseScalarSection k f c) M) p z = c • z := by
  have hlin : ((moduleGlobalSections X).rightDerived p).map
      (globalSmul (baseScalarSection k f c) M) = (baseScalarSection k f c) • 𝟙 _ := by
    rw [globalSmul_eq_smul_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  with_unfolding_all
    change (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).map
      (((moduleGlobalSections X).rightDerived p).map (globalSmul (baseScalarSection k f c) M)) z = _
    rw [hlin]
    rfl

end AlgebraicGeometry

end
