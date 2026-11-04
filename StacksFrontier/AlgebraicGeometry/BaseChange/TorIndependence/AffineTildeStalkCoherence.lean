module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineTildeStalkDerived
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionCoherence

/-!
# The two derived stalk computations of an affine pullback agree

For a ring map `c : A ⟶ A'` and a point `y` of `Spec A'`, the two derived-stalk computations of
`L(Spec c)^*(M̃^•)` at `y`, `AlgebraicGeometry.derivedAffineTildeStalkLeft` through `Spec A'` and
`AlgebraicGeometry.derivedAffineTildeStalkRight` through `Spec A`, are the same morphism of
functors on `D(A)`.

## Main results

* `StacksDraft.AffineTildeStalkChase.chase`: an eleven-step diagram chase in an arbitrary
  category, with every object and morphism a variable.
* `AlgebraicGeometry.derivedTildeStalkIso_inv_app_comp_comparison`: the inverse of the derived
  tilde-stalk isomorphism against the comparison of derived with degreewise extension of scalars.
* `AlgebraicGeometry.affinePullbackComparison_fac_app`: the affine pullback comparison at a
  complex, with its three comparisons spelled out.
* `AlgebraicGeometry.affineTildeStalkCompatibility_inv` and
  `AlgebraicGeometry.affineTildeStalkCompatibility_mapHomologicalComplex`: the compatibility of
  the tilde-stalk, affine-pullback and pullback-stalk isomorphisms, at a module and on complexes.
* `AlgebraicGeometry.derivedAffineTildeStalk_hcomp`: the two computations agree after
  composition with the comparison of derived against degreewise extension of scalars, at every
  cochain complex.
* `AlgebraicGeometry.derivedAffineTildeStalkLeft_eq_right`: the two computations agree.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedExtensionScalarsComp
open RingTheory.TorIndependence
open scoped ChangeOfRings

universe u w

namespace StacksDraft.AffineTildeStalkChase

variable {C : Type*} [Category* C]

/-! ### Composites with identities inserted

Each of these says that a composite with identities inserted is the composite without them. -/

/-- Three factors, with an identity before the first and before the second. -/
public theorem id_comp_id_comp3 {X₀ X₁ X₂ X₃ : C} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂)
    (f₃ : X₂ ⟶ X₃) : 𝟙 X₀ ≫ f₁ ≫ 𝟙 X₁ ≫ f₂ ≫ f₃ = f₁ ≫ f₂ ≫ f₃ := by
  simp

/-- Two factors, with an identity before each. -/
public theorem id_comp_id_comp2 {X₀ X₁ X₂ : C} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) :
    𝟙 X₀ ≫ f₁ ≫ 𝟙 X₁ ≫ f₂ = f₁ ≫ f₂ := by
  simp

/-- One factor, with an identity on each side. -/
public theorem id_comp_comp_id {X₀ X₁ : C} (f : X₀ ⟶ X₁) : 𝟙 X₀ ≫ f ≫ 𝟙 X₁ = f := by
  simp

/-- Four factors, with an identity before the second, the third and the fourth. -/
public theorem comp_id_comp3 {X₀ X₁ X₂ X₃ X₄ : C} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂)
    (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄) :
    f₁ ≫ 𝟙 X₁ ≫ f₂ ≫ 𝟙 X₂ ≫ f₃ ≫ 𝟙 X₃ ≫ f₄ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ := by
  simp

/-- Four factors, with an identity before the second only. -/
public theorem comp_id_comp4 {X₀ X₁ X₂ X₃ X₄ : C} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂)
    (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄) :
    f₁ ≫ 𝟙 X₁ ≫ f₂ ≫ f₃ ≫ f₄ = f₁ ≫ f₂ ≫ f₃ ≫ f₄ := by
  simp

/-! ### Transporting an equation of composites along equations of its factors -/

/-- A two-fold composite, factor by factor. -/
public theorem comp2_congr {X₀ X₁ X₂ : C} {g₁ f₁ : X₀ ⟶ X₁} {g₂ f₂ : X₁ ⟶ X₂}
    (h₁ : g₁ = f₁) (h₂ : g₂ = f₂) : g₁ ≫ g₂ = f₁ ≫ f₂ := by
  rw [h₁, h₂]

/-- An equation `a ≫ E = T ≫ R` with `E` and `R` renamed and `T` split in two. -/
public theorem comp_eq_comp3_of_eq {X₀ X₁ X₂ D₁ D₂ : C} (a : X₀ ⟶ X₁) {E E' : X₁ ⟶ X₂}
    {T : X₀ ⟶ D₂} (t₁ : X₀ ⟶ D₁) (t₂ : D₁ ⟶ D₂) {R R' : D₂ ⟶ X₂}
    (hE : E = E') (hT : T = t₁ ≫ t₂) (hR : R = R') (h : a ≫ E = T ≫ R) :
    a ≫ E' = t₁ ≫ t₂ ≫ R' := by
  rw [← hE, ← hR, ← Category.assoc, ← hT]
  exact h

/-- A functor carries an equation between a two-fold and a three-fold composite to the equation
between the composites of the images. -/
public theorem map_comp2_eq_comp3 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A₁ A₂ A₃ B₁ B₂ : D} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (p : A₁ ⟶ B₁) (q : B₁ ⟶ B₂)
    (r : B₂ ⟶ A₃) (h : a ≫ b = p ≫ q ≫ r) :
    F.map a ≫ F.map b = F.map p ≫ F.map q ≫ F.map r := by
  simp only [← Functor.map_comp]
  exact congrArg F.map h

/-- A functor carries an equation between a three-fold and a four-fold composite to the equation
between the composites of the images. -/
public theorem map_comp3_eq_comp4 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ : D} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c' : A₃ ⟶ A₄) (p : A₁ ⟶ B₁)
    (q : B₁ ⟶ B₂) (r : B₂ ⟶ B₃) (s : B₃ ⟶ A₄) (h : a ≫ b ≫ c' = p ≫ q ≫ r ≫ s) :
    F.map a ≫ F.map b ≫ F.map c' = F.map p ≫ F.map q ≫ F.map r ≫ F.map s := by
  simp only [← Functor.map_comp]
  exact congrArg F.map h

/-- If `e.hom ≫ f = cp ≫ m.hom` for isomorphisms `e` and `m`, then `e.inv ≫ cp = f ≫ m.inv`. -/
public theorem inv_comp_eq_comp_inv {X₀ X₁ X₂ X₃ : C} (e : X₀ ≅ X₁) (f : X₁ ⟶ X₂)
    (cp : X₀ ⟶ X₃) (m : X₃ ≅ X₂) (h : e.hom ≫ f = cp ≫ m.hom) :
    e.inv ≫ cp = f ≫ m.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A two-fold splitting whose middle pair cancels.** The composite `I ≫ cp` is
`m₁ ≫ m₂ ≫ m₃` once `I` is split as `g₁ ≫ g₂`, the first factor is presented as
`m₁ ≫ m₂ ≫ ν`, the second against `cp` as `f ≫ m₃`, and `ν ≫ f` is the identity. -/
public theorem split_cancel {X₀ X₁ X₂ X₃ M₁ M₂ : C} (I : X₀ ⟶ X₂) (g₁ : X₀ ⟶ X₁)
    (g₂ : X₁ ⟶ X₂) (cp : X₂ ⟶ X₃) (m₁ : X₀ ⟶ M₁) (m₂ : M₁ ⟶ M₂) (ν : M₂ ⟶ X₁) (f : X₁ ⟶ M₂)
    (m₃ : M₂ ⟶ X₃) (h₁ : g₁ = m₁ ≫ m₂ ≫ ν) (h₂ : g₂ ≫ cp = f ≫ m₃)
    (hνf : ν ≫ f = 𝟙 M₂) (hI : I = g₁ ≫ g₂) :
    I ≫ cp = m₁ ≫ m₂ ≫ m₃ := by
  rw [hI, h₁]
  simp only [Category.assoc]
  rw [h₂, reassoc_of% hνf]

/-- **A four-fold composite out of two isomorphisms, read backwards.** From
`α ≫ β ≫ γ ≫ δ = ρ₁ ≫ ρ₂ ≫ ρ₃` with `α`, `β` and `ρ₃` invertible, the composite `γ ≫ δ`
read against the inverse of `ρ₃` is `ρ₁ ≫ ρ₂` read against the inverses of `β` and `α`. -/
public theorem comp4_eq_comp3_inv {X₁ X₂ X₃ X₄ X₅ P₁ P₂ : C} (α : X₁ ≅ X₂) (β : X₂ ≅ X₃)
    (γ : X₃ ⟶ X₄) (δ : X₄ ⟶ X₅) (ρ₁ : X₁ ⟶ P₁) (ρ₂ : P₁ ⟶ P₂) (ρ₃ : P₂ ≅ X₅)
    (h : α.hom ≫ β.hom ≫ γ ≫ δ = ρ₁ ≫ ρ₂ ≫ ρ₃.hom) :
    γ ≫ δ ≫ ρ₃.inv = β.inv ≫ α.inv ≫ ρ₁ ≫ ρ₂ := by
  rw [Iso.eq_inv_comp, Iso.eq_inv_comp]
  simp only [← Category.assoc]
  rw [Iso.comp_inv_eq]
  simpa only [Category.assoc] using h

/-! ### The chase -/

/-- **An eleven-step diagram chase.** The composite `l₁ ≫ l₂ ≫ l₃ ≫ t` equals
`r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ t` whenever the eleven equations `h₁`, …, `h₁₁` hold. -/
public theorem chase {O₀ O₁ O₂ O₃ O₄ B₁ B₂ C₁ C₂ C₃ D₁ D₂ E₁ W₁ W₂ W₃
      Y₁ Y₂ Z₁ Z₂ Z₃ Z₄ : C}
    (l₁ : O₀ ⟶ O₁) (l₂ : O₁ ⟶ O₂) (l₃ : O₂ ⟶ O₃) (t : O₃ ⟶ O₄)
    (r₁ : O₀ ⟶ W₁) (r₂ : W₁ ⟶ W₂) (r₃ : W₂ ⟶ W₃) (r₄ : W₃ ⟶ O₃)
    (u₁ : O₂ ⟶ B₁) (u₂ : B₁ ⟶ B₂) (u₃ : B₂ ⟶ O₄)
    (v₁ : O₁ ⟶ C₁) (v₂ : C₁ ⟶ B₁)
    (w₁ : C₁ ⟶ C₂) (w₂ : C₂ ⟶ C₃) (w₃ : C₃ ⟶ B₂)
    (p₁ : O₀ ⟶ D₁) (p₂ : D₁ ⟶ D₂) (p₃ : D₂ ⟶ C₂)
    (q₁ : D₂ ⟶ E₁) (q₂ : E₁ ⟶ C₃) (q₂' : E₁ ⟶ Z₄)
    (s₁ : W₂ ⟶ Z₁) (s₂ : Z₁ ⟶ Z₂) (s₃ : Z₂ ⟶ Z₃) (s₄ : Z₃ ⟶ O₄)
    (n₁ : W₁ ⟶ Y₁) (n₂ : Y₁ ⟶ Y₂) (n₃ : Y₂ ⟶ Z₁) (z : D₁ ⟶ Y₁)
    (y₁ : Y₂ ⟶ Z₄) (y₂ : Z₄ ⟶ Z₂)
    (h₁ : l₃ ≫ t = u₁ ≫ u₂ ≫ u₃) (h₂ : l₂ ≫ u₁ = v₁ ≫ v₂)
    (h₃ : v₂ ≫ u₂ = w₁ ≫ w₂ ≫ w₃) (h₄ : l₁ ≫ v₁ ≫ w₁ = p₁ ≫ p₂ ≫ p₃)
    (h₅ : p₃ ≫ w₂ = q₁ ≫ q₂) (h₆ : r₃ ≫ r₄ ≫ t = s₁ ≫ s₂ ≫ s₃ ≫ s₄)
    (h₇ : r₂ ≫ s₁ = n₁ ≫ n₂ ≫ n₃) (h₈ : r₁ ≫ n₁ = p₁ ≫ z)
    (h₉ : n₃ ≫ s₂ = y₁ ≫ y₂) (h₁₀ : z ≫ n₂ ≫ y₁ = p₂ ≫ q₁ ≫ q₂')
    (h₁₁ : q₂ ≫ w₃ ≫ u₃ = q₂' ≫ y₂ ≫ s₃ ≫ s₄) :
    (l₁ ≫ l₂ ≫ l₃) ≫ t = (r₁ ≫ r₂ ≫ r₃ ≫ r₄) ≫ t := by
  simp only [Category.assoc]
  have hl : l₁ ≫ l₂ ≫ l₃ ≫ t = p₁ ≫ p₂ ≫ q₁ ≫ q₂' ≫ y₂ ≫ s₃ ≫ s₄ := by
    rw [h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅, h₁₁]
  have hr : r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ t = p₁ ≫ p₂ ≫ q₁ ≫ q₂' ≫ y₂ ≫ s₃ ≫ s₄ := by
    rw [h₆, reassoc_of% h₇, reassoc_of% h₈, reassoc_of% h₉, reassoc_of% h₁₀]
  rw [hl, hr]

end StacksDraft.AffineTildeStalkChase

namespace ModuleCat

/-- **The transport along an equality of ring homomorphisms is a transport of objects.** At a
module, `ModuleCat.extendScalarsFunctorCongr` is the `eqToHom` of the equality of the two
extensions of that module. -/
public theorem extendScalarsFunctorCongr_hom_app_eq_eqToHom {R S : Type u} [CommRing R]
    [CommRing S] {f g : R →+* S} (h : f = g) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalarsFunctorCongr.{u} h).hom.app M =
      eqToHom (congrArg (fun ψ => (ModuleCat.extendScalars.{u, u, u} ψ).obj M) h) := by
  subst h
  simp [ModuleCat.extendScalarsFunctorCongr]

end ModuleCat

namespace StacksDraft.DerivedExtensionScalarsComp

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
  [HasDerivedCategory.{w} (ModuleCat.{u} T)]

/-- **The characterizing equation of the composition isomorphism for derived extension of
scalars, with the transport along an equality of ring homomorphisms as a separate factor.**
For `h : b.comp a = φ`, the composite of `derivedExtensionScalarsCompIsoGeneral a b`, the
`eqToHom` of derived functors induced by `h`, and the comparison map for `φ` equals the composite
of the comparison maps for `a` and `b`, `extensionScalarsComplexCompIsoGeneral a b`, and the
`eqToHom` of complexes induced by `h`. -/
public theorem derivedExtensionScalarsCompIso_app_eqToHom_comp_comparison
    (a : R →+* S) (b : S →+* T) (φ : R →+* T) (h : b.comp a = φ)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompIsoGeneral a b).hom.app (DerivedCategory.Q.obj C) ≫
        (eqToHom (congrArg
            (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor) h)).app
          (DerivedCategory.Q.obj C) ≫
        (totalDerivedExtensionScalars.{u, u, u} φ).comparison.app C =
      (totalDerivedExtensionScalars.{u, u, u} b).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} a).comparison.app C) ≫
        (totalDerivedExtensionScalars.{u, u, u} b).comparison.app
          (((ModuleCat.extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        (extensionScalarsComplexCompIsoGeneral a b).hom.app C ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj C) h) := by
  subst h
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp]
  exact Eq.trans (derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison a b C)
    (StacksDraft.CompositionChase.comp3_congr_third _ _ _ _ (Category.comp_id _).symm)

end StacksDraft.DerivedExtensionScalarsComp

namespace AlgebraicGeometry

open Stacks.ModuleSkyscraper

/-! ### The derived tilde-stalk isomorphism against the derived-functor comparison -/

/-- At a cochain complex of `A`-modules, the inverse of `AlgebraicGeometry.derivedTildeStalkIso`
followed by the comparison of derived with degreewise extension of scalars along the germ map is
the degreewise factorization of `tilde.functor A`, then that of the stalk functor, then
`AlgebraicGeometry.tildeModulesStalkIso` applied degreewise. -/
public theorem derivedTildeStalkIso_inv_app_comp_comparison (A : CommRingCat.{u})
    (y : (Spec A).carrier) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedTildeStalkIso A y).inv.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom A y)).comparison.app P =
      (derivedStalkFunctor y).map ((tilde.functor A).mapDerivedCategoryFactors.hom.app P) ≫
        (modulesStalkFunctor (Spec A) y).mapDerivedCategoryFactors.hom.app
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (tildeModulesStalkIso A y).hom
          (ComplexShape.up ℤ)).app P) :=
  StacksDraft.AffineTildeStalkChase.split_cancel _ _ _ _ _ _ _ _ _
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q (tilde.functor A)
      (modulesStalkFunctor (Spec A) y) P)
    (StacksDraft.AffineTildeStalkChase.inv_comp_eq_comp_inv
      ((totalDerivedExtensionScalarsIsoMapDerivedCategory (specGermRingHom A y)
        (tilde.functor A ⋙ modulesStalkFunctor (Spec A) y)
        (tildeModulesStalkIso A y)).app (DerivedCategory.Q.obj P)) _ _
      ((mapHomologicalComplexIsoOfExtendScalars (specGermRingHom A y)
        (tilde.functor A ⋙ modulesStalkFunctor (Spec A) y) (tildeModulesStalkIso A y)).app P)
      (totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors (specGermRingHom A y)
        (tilde.functor A ⋙ modulesStalkFunctor (Spec A) y) (tildeModulesStalkIso A y) P))
    ((tilde.functor A ⋙
      modulesStalkFunctor (Spec A) y).mapDerivedCategoryFactors.inv_hom_id_app P)
    rfl

/-! ### The affine pullback comparison, with its factors spelled out -/

variable {A A' : CommRingCat.{u}} (c : A ⟶ A') (y : (Spec A').carrier)

/-- **The two presentations of the comparison from derived to degreewise pullback agree.** The
component of `Stacks.DerivedPullback.derivedPullbackComplexComparison` is
`AlgebraicGeometry.pullbackComparisonOnComplex`. -/
public theorem derivedPullbackComplexComparison_app (P : CochainComplex (Spec A).Modules ℤ) :
    (Stacks.DerivedPullback.derivedPullbackComplexComparison
        (Spec.map c).toLRSHom.toShHom).app P =
      pullbackComparisonOnComplex (Spec.map c) P :=
  StacksDraft.AffineTildeStalkChase.comp_id_comp3 _ _ _ _

/-- **The affine pullback comparison, with its three comparisons spelled out.** This is
`AlgebraicGeometry.affinePullbackComparison_fac` with
`AlgebraicGeometry.extendScalarsTildeComparison`,
`AlgebraicGeometry.tildeDerivedPullbackComparison` and
`AlgebraicGeometry.tildePullbackComplexCompQIso` evaluated at a complex: the two derived-functor
comparisons and the degreewise affine-pullback isomorphism
`AlgebraicGeometry.tildePullbackComplexIso`. -/
public theorem affinePullbackComparison_fac_app (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affinePullbackComparison A A' c).hom.app (DerivedCategory.Q.obj P) ≫
        (tilde.functor A').mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} c.hom).comparison.app P) ≫
        (tilde.functor A').mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} c.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (Stacks.Duality.derivedPullback (Spec.map c)).map
          ((tilde.functor A).mapDerivedCategoryFactors.hom.app P) ≫
        pullbackComparisonOnComplex (Spec.map c)
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((tildePullbackComplexIso A A' c).hom.app P) :=
  StacksDraft.AffineTildeStalkChase.comp_eq_comp3_of_eq _ _ _
    (StacksDraft.AffineTildeStalkChase.id_comp_id_comp2 _ _)
    (StacksDraft.AffineTildeStalkChase.comp2_congr
      (StacksDraft.AffineTildeStalkChase.id_comp_comp_id _)
      (derivedPullbackComplexComparison_app c _))
    (StacksDraft.AffineTildeStalkChase.id_comp_comp_id _)
    (affinePullbackComparison_fac A A' c P)

/-! ### The compatibility at a module and on complexes -/

/-- This is `AlgebraicGeometry.affineTildeStalkCompatibility` rearranged: the extension along the
germ of `Spec c` of `AlgebraicGeometry.tildeModulesStalkIso` at `A` and
`AlgebraicGeometry.pullbackStalkIso` move to the other side as their inverses, and the merge of
the two extensions of scalars along `A ⟶ A' ⟶ 𝒪_{Spec A',y}` moves across as its inverse. -/
public theorem affineTildeStalkCompatibility_inv (M : ModuleCat.{u} A) :
    (modulesStalkFunctor (Spec A') y).map ((pullbackTildeIso A A' c).hom.app M) ≫
        (tildeModulesStalkIso A' y).hom.app ((ModuleCat.extendScalars.{u, u, u} c.hom).obj M) ≫
        (ModuleCat.extendScalarsComp.{u, u} c.hom (specGermRingHom A' y)).inv.app M =
      (pullbackStalkIso (Spec.map c) y).inv.app ((tilde.functor A).obj M) ≫
        (ModuleCat.extendScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).map
          ((tildeModulesStalkIso A ((Spec.map c).base y)).hom.app M) ≫
        (ModuleCat.extendScalarsComp.{u, u} (specGermRingHom A ((Spec.map c).base y))
          ((Spec.map c).stalkMap y).hom).inv.app M ≫
        eqToHom (congrArg (fun ψ => (ModuleCat.extendScalars.{u, u, u} ψ).obj M)
          (specGermRingHom_stalkMap c y)) := by
  have h := affineTildeStalkCompatibility c y M
  rw [ModuleCat.extendScalarsFunctorCongr_hom_app_eq_eqToHom] at h
  exact StacksDraft.AffineTildeStalkChase.comp4_eq_comp3_inv
    (((ModuleCat.extendScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).mapIso
      ((tildeModulesStalkIso A ((Spec.map c).base y)).app M)).symm)
    ((pullbackStalkIso (Spec.map c) y).app ((tilde.functor A).obj M)) _ _ _ _
    ((ModuleCat.extendScalarsComp.{u, u} c.hom (specGermRingHom A' y)).app M) h

/-- `AlgebraicGeometry.affineTildeStalkCompatibility_inv` applied degreewise, with
`CategoryTheory.Functor.mapHomologicalComplexCompIso` identifying the factors whose functors are
composites. -/
public theorem affineTildeStalkCompatibility_mapHomologicalComplex
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((modulesStalkFunctor (Spec A') y).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((tildePullbackComplexIso A A' c).hom.app P) ≫
        (NatTrans.mapHomologicalComplex (tildeModulesStalkIso A' y).hom
            (ComplexShape.up ℤ)).app
          (((ModuleCat.extendScalars.{u, u, u} c.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (Functor.mapHomologicalComplexCompIso
          (ModuleCat.extendScalarsComp.{u, u} c.hom (specGermRingHom A' y)).symm
          (ComplexShape.up ℤ)).hom.app P =
      (NatIso.mapHomologicalComplex (pullbackStalkIso (Spec.map c) y).symm
            (ComplexShape.up ℤ)).hom.app
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.extendScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (tildeModulesStalkIso A ((Spec.map c).base y)).hom (ComplexShape.up ℤ)).app P) ≫
        (Functor.mapHomologicalComplexCompIso
            (ModuleCat.extendScalarsComp.{u, u} (specGermRingHom A ((Spec.map c).base y))
              ((Spec.map c).stalkMap y).hom).symm (ComplexShape.up ℤ)).hom.app P ≫
        eqToHom (congrArg (fun ψ => ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) (specGermRingHom_stalkMap c y)) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Iso.symm_hom, tildePullbackComplexIso, Iso.trans_hom, NatTrans.comp_app, NatTrans.id_app,
    Iso.refl_hom]
  exact affineTildeStalkCompatibility_inv c y (P.X i)

/-! ### The two routes, componentwise -/

/-- The three factors of the first route at an object of `D(A)`: the affine comparison square read
in the stalk, the inverse of the derived tilde-stalk isomorphism at `A'`, and the merge of the two
derived extensions of scalars. -/
public theorem derivedAffineTildeStalkLeft_app (K : DerivedCategory (ModuleCat.{u} A)) :
    (derivedAffineTildeStalkLeft c y).app K =
      (derivedStalkFunctor y).map ((affinePullbackComparison A A' c).hom.app K) ≫
        (derivedTildeStalkIso A' y).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} c.hom).functor.obj K) ≫
        (derivedExtensionScalarsCompIsoGeneral c.hom (specGermRingHom A' y)).hom.app K :=
  StacksDraft.AffineTildeStalkChase.id_comp_id_comp3 _ _ _

/-- The four factors of the second route at an object of `D(A)`: the derived stalk formula for
`Spec c`, the inverse of the derived tilde-stalk isomorphism at `A` extended along the germ of
`Spec c`, the merge of the two derived extensions of scalars, and the transport along
`AlgebraicGeometry.specGermRingHom_stalkMap`. -/
public theorem derivedAffineTildeStalkRight_app (K : DerivedCategory (ModuleCat.{u} A)) :
    (derivedAffineTildeStalkRight c y).app K =
      (derivedPullbackStalkIso (Spec.map c) y).hom.app
          ((tilde.functor A).mapDerivedCategory.obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).functor.map
          ((derivedTildeStalkIso A ((Spec.map c).base y)).inv.app K) ≫
        (derivedExtensionScalarsCompIsoGeneral (specGermRingHom A ((Spec.map c).base y))
            ((Spec.map c).stalkMap y).hom).hom.app K ≫
        (eqToHom (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
          (specGermRingHom_stalkMap c y))).app K :=
  StacksDraft.AffineTildeStalkChase.comp_id_comp4 _ _ _ _

/-! ### The equation, and the coherence -/

/-- At every cochain complex of `A`-modules, with no K-flatness assumed, the two routes agree
after composition with the comparison of derived against degreewise extension of scalars along the
composite germ map `A ⟶ 𝒪_{Spec A',y}`. -/
public theorem derivedAffineTildeStalk_hcomp (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedAffineTildeStalkLeft c y).app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u}
          ((specGermRingHom A' y).comp c.hom)).comparison.app P =
      (derivedAffineTildeStalkRight c y).app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u}
          ((specGermRingHom A' y).comp c.hom)).comparison.app P := by
  rw [derivedAffineTildeStalkLeft_app, derivedAffineTildeStalkRight_app]
  have h₁ := derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison c.hom
    (specGermRingHom A' y) P
  have h₂ := ((derivedTildeStalkIso A' y).inv.naturality
    ((totalDerivedExtensionScalars.{u, u, u} c.hom).comparison.app P)).symm
  have h₃ := derivedTildeStalkIso_inv_app_comp_comparison A' y
    (((ModuleCat.extendScalars.{u, u, u} c.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  have h₄ := StacksDraft.CompositionChase.map_comp_three (derivedStalkFunctor y) _ _ _ _ _ _
    (affinePullbackComparison_fac_app c P)
  have h₅ := (modulesStalkFunctor (Spec A') y).mapDerivedCategoryFactors.hom.naturality
    ((tildePullbackComplexIso A A' c).hom.app P)
  have h₆ := derivedExtensionScalarsCompIso_app_eqToHom_comp_comparison
    (specGermRingHom A ((Spec.map c).base y)) ((Spec.map c).stalkMap y).hom
    ((specGermRingHom A' y).comp c.hom) (specGermRingHom_stalkMap c y) P
  have h₇ := StacksDraft.AffineTildeStalkChase.map_comp2_eq_comp3
    (totalDerivedExtensionScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).functor _ _ _ _ _
    (derivedTildeStalkIso_inv_app_comp_comparison A ((Spec.map c).base y) P)
  have h₈ := ((derivedPullbackStalkIso (Spec.map c) y).hom.naturality
    ((tilde.functor A).mapDerivedCategoryFactors.hom.app P)).symm
  have h₉ := (totalDerivedExtensionScalars.{u, u, u}
    ((Spec.map c).stalkMap y).hom).comparison.naturality
      ((NatTrans.mapHomologicalComplex
        (tildeModulesStalkIso A ((Spec.map c).base y)).hom (ComplexShape.up ℤ)).app P)
  have h₁₀ := derivedPullbackStalkIso_comp_comparison (Spec.map c) y
    (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have h₁₁ := StacksDraft.AffineTildeStalkChase.map_comp3_eq_comp4 DerivedCategory.Q
    _ _ _ _ _ _ _ (affineTildeStalkCompatibility_mapHomologicalComplex c y P)
  have h₆' := h₆.trans (StacksDraft.CompositionChase.comp4_congr_fourth _ _ _ _ _
    (StacksDraft.CompositionChase.map_eqToHom_eq DerivedCategory.Q
      (congrArg (fun ψ => ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) (specGermRingHom_stalkMap c y)) _))
  exact StacksDraft.AffineTildeStalkChase.chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆' h₇ h₈ h₉ h₁₀ h₁₁

/-- **The two derived stalk computations of an affine pullback agree.** The two
derived-stalk computations of `L(Spec c)^*(M̃^•)` at `y` — through `Spec A'` by the affine
comparison square, and through `Spec A` by the derived stalk formula — are the same morphism of
functors on `D(A)`. -/
public theorem derivedAffineTildeStalkLeft_eq_right :
    derivedAffineTildeStalkLeft c y = derivedAffineTildeStalkRight c y :=
  derivedAffineTildeStalk_eq_of_comparison c y fun P _ => derivedAffineTildeStalk_hcomp c y P

end AlgebraicGeometry

end
