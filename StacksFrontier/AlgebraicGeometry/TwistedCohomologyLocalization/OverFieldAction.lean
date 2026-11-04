module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionLinear
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.GradedModule
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# Multiplication by a global section of a tensor power, on cohomology over a field

Let `k` be a field, `X` a scheme over `k` through `f : X ⟶ Spec k`, `ℒ` an invertible
`𝒪_X`-module and `ℱ` an `𝒪_X`-module. A global section `s` of `ℒ^{⊗ n}` multiplies the twist
`ℱ ⊗ ℒ^{⊗ j}` into `ℱ ⊗ ℒ^{⊗ (n + j)}`
(`Stacks.SheafOfModules.TwistAction.actionOf`), hence acts on the `k`-linear cohomology
`H^p(X, ℱ ⊗ ℒ^{⊗ j})` of `AlgebraicGeometry.cohomologyOverField`. This file shows that the
resulting map is **`k`-linear in the section** and packages it as a `k`-linear map
`Γ(X, ℒ^{⊗ n}) →ₗ[k] (H^p(X, ℱ ⊗ ℒ^{⊗ j}) →ₗ[k] H^p(X, ℱ ⊗ ℒ^{⊗ (n + j)}))`, and that
multiplication by two global sections commutes.

Additivity in the section is the additivity of `actionOf` together with the additivity of the
right derived functors of global sections. Homogeneity is genuinely more: it needs the
`Γ(X, ⊤)`-linearity of those derived functors, which is obtained here by giving the category of
sheaves of modules on `X` its `k`-linear structure -- a scalar `c` acts by multiplication by the
global function `f^♯(c)` -- and transporting it through
`CategoryTheory.Functor.linear_rightDerived`. The two halves meet in
`Stacks.TwistActionLinear.actionOf_smul`, which turns multiplying by `r • s` into multiplying by
the global function `r` followed by multiplying by `s`.

## Main definitions

* `Stacks.Cohomology.TwistCohomologyAction.scalarSmul`: multiplication by the image of a scalar,
  as an endomorphism of a sheaf of modules.
* `Stacks.Cohomology.TwistCohomologyAction.twistSectionSpace`: the global sections of
  `ℒ^{⊗ n}`, as a `k`-vector space.
* `Stacks.Cohomology.TwistCohomologyAction.modulesLinear`: the `k`-linear structure on the
  sheaves of modules on a scheme over `k`.
* `Stacks.Cohomology.TwistCohomologyAction.twistCohomologyAction`: **the `k`-linear action of
  the global sections of `ℒ^{⊗ n}` on the cohomology of the twists.**

## Main results

* `Stacks.Cohomology.TwistCohomologyAction.cohomologyOverFieldMap_actionOf_add` and
  `cohomologyOverFieldMap_actionOf_smul`: the induced map on cohomology over `k` is additive
  and homogeneous in the multiplying section.
* `Stacks.Cohomology.TwistCohomologyAction.map_scalarSmul_apply`: **the map induced on
  cohomology by multiplication by the global function `f^♯(c)` is multiplication by `c`.** This
  is the linearity of the derived global sections.
* `Stacks.Cohomology.TwistCohomologyAction.cohomologyOverFieldMap_actionOf_comm`: the
  commutation law, read on cohomology over `k`.

## Implementation notes

The twist is `Stacks.Cohomology.TwistedGradedModule.twist`, the one the graded cohomology module
is built from. It is *not* definitionally equal to
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule`: the two are built from different
spellings of the tensor power.

The `k`-linear structures of `modulesLinear` and of `ModuleCat.linearOverField` depend on the
structure morphism `f`, which no instance search can recover from a sheaf of modules. They are
therefore `def`s, introduced as local instances inside `map_scalarSmul_apply`.

Multiplication by a scalar is multiplication by its image global function over the *categorical*
terminal open `⊤_ (Opens X)`, because that is the object over which `actionOf` takes its
sections, while `AlgebraicGeometry.cohomologyOverField` restricts scalars along the structure map
to `Γ(X, ⊤)`. `baseSection_restrict` crosses the two, by the composition law
`AlgebraicGeometry.Scheme.Hom.appLE_map` for `appLE`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  MonoidalCategory
open Stacks.Cohomology Stacks.SheafOfModules Stacks.SheafOfModules.TwistAction
  Stacks.TwistActionLinear

universe v u w

namespace Stacks.Cohomology.TwistCohomologyAction

section OverField

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- Global sections of modules on `X`; its right derived functors are cohomology. -/
abbrev Sec (X : Scheme.{u}) :
    _root_.SheafOfModules.{u} X.ringCatSheaf ⥤
      ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) :=
  _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))

/-- The right derived functors of global sections are additive. -/
instance additive_derived (X : Scheme.{u}) (p : ℕ) : ((Sec X).rightDerived p).Additive :=
  Functor.additive_rightDerived _ p

/-- The structure ring map of a scheme over `k`. -/
abbrev baseRingHom : CommRingCat.of k ⟶ X.presheaf.obj (op (⊤ : X.Opens)) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)

/-- **`cohomologyOverFieldMap` is additive in the morphism.** -/
theorem cohomologyOverFieldMap_add (p : ℕ) {A B : X.Modules} (φ ψ : A ⟶ B) :
    cohomologyOverFieldMap k f (φ + ψ) p =
      cohomologyOverFieldMap k f φ p + cohomologyOverFieldMap k f ψ p := by
  unfold cohomologyOverFieldMap
  exact (congrArg (ModuleCat.restrictScalars (baseRingHom k f).hom).map
    (Functor.map_add ((Sec X).rightDerived p))).trans
    (Functor.map_add (ModuleCat.restrictScalars (baseRingHom k f).hom))

/-- Functoriality of `cohomologyOverFieldMap` on a triple composite. -/
theorem cohomologyOverFieldMap_comp₃ (p : ℕ) {A B D E : X.Modules}
    (φ : A ⟶ B) (ψ : B ⟶ D) (ρ : D ⟶ E) :
    cohomologyOverFieldMap k f (φ ≫ ψ ≫ ρ) p =
      cohomologyOverFieldMap k f φ p ≫ cohomologyOverFieldMap k f ψ p ≫
        cohomologyOverFieldMap k f ρ p :=
  (cohomologyOverFieldMap_comp k f φ (ψ ≫ ρ) p).trans
    (congrArg (fun α => cohomologyOverFieldMap k f φ p ≫ α)
      (cohomologyOverFieldMap_comp k f ψ ρ p))

/-- The image of a scalar in the global functions, in the `RingCat` spelling. -/
abbrev baseScalar (c : k) : X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) := (baseRingHom k f).hom c

/-- The structure ring map of a scheme over `k`, read over the categorical terminal open. -/
abbrev baseSectionHom : CommRingCat.of k ⟶ (sectionSiteRing X).obj (op (⊤_ X.Opens)) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ (⊤_ X.Opens) (by simp)

/-- The image in `Γ(X, ⊤_)` of a scalar. -/
abbrev baseSection (c : k) : (sectionSiteRing X).obj (op (⊤_ X.Opens)) :=
  (baseSectionHom k f).hom c

/-- Restricting the image of a scalar from the categorical terminal open to `⊤`. -/
theorem baseSection_restrict (c : k) :
    (sectionSiteRing X).map (terminal.from (⊤ : X.Opens)).op (baseSection k f c) =
      baseScalar k f c := by
  have h := Scheme.Hom.appLE_map f (U := (⊤ : (Spec (CommRingCat.of k)).Opens))
    (V := (⊤_ X.Opens)) (V' := (⊤ : X.Opens)) (by simp) (terminal.from (⊤ : X.Opens)).op
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) h

/-- The image of the unit scalar is the unit global function. -/
theorem baseSection_one : baseSection k f (1 : k) = 1 := map_one _

/-- The image of a product of scalars is the product of the images. -/
theorem baseSection_mul (c c' : k) :
    baseSection k f (c * c') = baseSection k f c * baseSection k f c' := map_mul _ _ _

/-- The image of a sum of scalars is the sum of the images. -/
theorem baseSection_add (c c' : k) :
    baseSection k f (c + c') = baseSection k f c + baseSection k f c' := map_add _ _ _

/-- The image of the zero scalar is the zero global function. -/
theorem baseSection_zero : baseSection k f (0 : k) = 0 := map_zero _

/-- Multiplication by the image of a scalar, as an endomorphism of a sheaf of modules. -/
abbrev scalarSmul (c : k) (M : _root_.SheafOfModules.{u} X.ringCatSheaf) : M ⟶ M :=
  sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c) M

/-- The `k`-linear structure on the sheaves of modules on a scheme over `k`. -/
@[instance_reducible] def modulesLinear :
    CategoryTheory.Linear k (_root_.SheafOfModules.{u} X.ringCatSheaf) where
  homModule M N :=
    { smul := fun c φ => scalarSmul k f c M ≫ φ
      one_smul := fun φ => by
        change scalarSmul k f (1 : k) M ≫ φ = φ
        exact (congrArg (fun ψ => ψ ≫ φ)
          ((congrArg (fun r => sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) r M)
            (baseSection_one k f)).trans
              (sectionSmul_one (sectionSiteRing X) (sectionSiteSheaf X) M))).trans
          (Category.id_comp φ)
      mul_smul := fun c c' φ => by
        change scalarSmul k f (c * c') M ≫ φ = scalarSmul k f c M ≫ scalarSmul k f c' M ≫ φ
        exact (congrArg (fun ψ => ψ ≫ φ)
          ((congrArg (fun r => sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) r M)
            (baseSection_mul k f c c')).trans
              (sectionSmul_mul (sectionSiteRing X) (sectionSiteSheaf X) _ _ M))).trans
          (Category.assoc _ _ _)
      smul_zero := fun _ => Limits.comp_zero
      smul_add := fun _ φ ψ => Preadditive.comp_add _ _ _ _ _ _
      add_smul := fun c c' φ => by
        change scalarSmul k f (c + c') M ≫ φ = scalarSmul k f c M ≫ φ + scalarSmul k f c' M ≫ φ
        exact (congrArg (fun ψ => ψ ≫ φ)
          ((congrArg (fun r => sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) r M)
            (baseSection_add k f c c')).trans
              (sectionSmul_add (sectionSiteRing X) (sectionSiteSheaf X) _ _ M))).trans
          (Preadditive.add_comp _ _ _ _ _ _)
      zero_smul := fun φ => by
        change scalarSmul k f (0 : k) M ≫ φ = 0
        exact (congrArg (fun ψ => ψ ≫ φ)
          ((congrArg (fun r => sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) r M)
            (baseSection_zero k f)).trans
              (sectionSmul_zero (sectionSiteRing X) (sectionSiteSheaf X) M))).trans
          Limits.zero_comp }
  smul_comp M N P c φ ψ := by
    change (sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c) M ≫ φ) ≫ ψ =
      sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c) M ≫ φ ≫ ψ
    exact Category.assoc _ _ _
  comp_smul M N P φ c ψ := by
    change φ ≫ (sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c) N ≫ ψ) =
      sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c) M ≫ φ ≫ ψ
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun α => α ≫ ψ) (comp_sectionSmul (sectionSiteRing X) (sectionSiteSheaf X)
        (baseSection k f c) φ)).trans (Category.assoc _ _ _))

/-- **The map induced on cohomology by multiplication by the image of a scalar is multiplication
by that scalar.** -/
theorem map_scalarSmul_apply (p : ℕ) (c : k) (A : _root_.SheafOfModules.{u} X.ringCatSheaf)
    (x : ((Sec X).rightDerived p).obj A) :
    ((Sec X).rightDerived p).map (scalarSmul k f c A) x = baseScalar k f c • x := by
  let : Algebra k (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) :=
    RingHom.toAlgebra (baseRingHom k f).hom
  let : CategoryTheory.Linear k (_root_.SheafOfModules.{u} X.ringCatSheaf) := modulesLinear k f
  let : CategoryTheory.Linear k
      (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) := ModuleCat.linearOverField
  have : Functor.Linear k (Sec X) :=
    { map_smul := fun φ c' => ModuleCat.hom_ext <| LinearMap.ext fun y => by
        change φ.val.app (op (⊤ : X.Opens))
          ((sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c') _).val.app
            (op (⊤ : X.Opens)) y) = _
        refine Eq.trans (congrArg (φ.val.app (op (⊤ : X.Opens)))
          ((sectionSmul_app (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c') _
              (op (⊤ : X.Opens)) y).trans
            (congrArg (fun r : X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) => r • y)
              (baseSection_restrict k f c')))) ?_
        exact LinearMap.map_smul (φ.val.app (op (⊤ : X.Opens))).hom (baseScalar k f c') y }
  have : Functor.Linear k ((Sec X).rightDerived p) := Functor.linear_rightDerived _ p
  have h2 : (c : k) • (𝟙 A) = scalarSmul k f c A := Category.comp_id _
  have h : ((Sec X).rightDerived p).map (c • (𝟙 A)) = c • ((Sec X).rightDerived p).map (𝟙 A) :=
    Functor.map_smul _ c (𝟙 A)
  rw [CategoryTheory.Functor.map_id, h2] at h
  exact congrArg (fun φ => ModuleCat.Hom.hom φ x) h

section Twist

variable (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible (sectionSiteRing X) (sectionSiteSheaf X) L] (F : X.Modules)

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- Global sections of `L^{⊗ n}` as a `k`-vector space. -/
abbrev twistSectionSpace (n : ℤ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (baseSectionHom k f).hom).obj
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n).val.obj
      (op (⊤_ X.Opens)))

/-- **The map induced on cohomology over `k` by multiplication by a global section of
`ℒ^{⊗ n}` is additive in that section.** -/
theorem cohomologyOverFieldMap_actionOf_add (p : ℕ) (n j : ℤ)
    (s s' : twistSectionSpace k f L n) :
    cohomologyOverFieldMap k f
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j (s + s')) p =
      cohomologyOverFieldMap k f (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) p +
        cohomologyOverFieldMap k f
          (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s') p :=
  (congrArg (fun φ => cohomologyOverFieldMap k f φ p)
    (actionOf_add (sectionSiteRing X) (sectionSiteSheaf X) L F n j s s')).trans
    (cohomologyOverFieldMap_add k f p _ _)

/-- Multiplication by a scalar multiple of a global section, read on a cohomology class of the
right derived global sections. -/
theorem map_actionOf_smul_apply (p : ℕ) (n j : ℤ) (c : k)
    (s : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n).val.obj
      (op (⊤_ X.Opens)))
    (x : ((Sec X).rightDerived p).obj (TwistedGradedModule.twist X L F j)) :
    ((Sec X).rightDerived p).map
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j (baseSection k f c • s)) x =
      baseScalar k f c • ((Sec X).rightDerived p).map
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) x := by
  refine Eq.trans (congrArg (fun φ : TwistedGradedModule.twist X L F j ⟶
      TwistedGradedModule.twist X L F (n + j) => ((Sec X).rightDerived p).map φ x)
    (actionOf_smul (sectionSiteRing X) (sectionSiteSheaf X) L F n j (baseSection k f c) s)) ?_
  refine Eq.trans (congrArg (fun g : ((Sec X).rightDerived p).obj
      (TwistedGradedModule.twist X L F j) ⟶
      ((Sec X).rightDerived p).obj (TwistedGradedModule.twist X L F (n + j)) => g x)
    (CategoryTheory.Functor.map_comp ((Sec X).rightDerived p)
      (sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c)
        (TwistedGradedModule.twist X L F j))
      (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s))) ?_
  change ((Sec X).rightDerived p).map
      (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s)
      (((Sec X).rightDerived p).map
        (sectionSmul (sectionSiteRing X) (sectionSiteSheaf X) (baseSection k f c)
          (TwistedGradedModule.twist X L F j)) x) = _
  exact (congrArg (fun z : ((Sec X).rightDerived p).obj (TwistedGradedModule.twist X L F j) =>
      ((Sec X).rightDerived p).map
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) z)
    (map_scalarSmul_apply k f p c (TwistedGradedModule.twist X L F j) x)).trans
    (LinearMap.map_smul (ModuleCat.Hom.hom (((Sec X).rightDerived p).map
      (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s))) (baseScalar k f c) x)

/-- **The map induced on cohomology over `k` by multiplication by a global section of
`ℒ^{⊗ n}` is homogeneous in that section**, read on a cohomology class. -/
theorem cohomologyOverFieldMap_actionOf_smul_apply (p : ℕ) (n j : ℤ) (c : k)
    (s : twistSectionSpace k f L n)
    (x : cohomologyOverField k f (TwistedGradedModule.twist X L F j) p) :
    (cohomologyOverFieldMap k f
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j (c • s)) p).hom x =
      c • (cohomologyOverFieldMap k f
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) p).hom x := by
  unfold cohomologyOverFieldMap
  simp only [ModuleCat.restrictScalars.smul_def]
  exact map_actionOf_smul_apply k f L F p n j c s x

/-- **The map induced on cohomology over `k` by multiplication by a global section of
`ℒ^{⊗ n}` is homogeneous in that section.** -/
theorem cohomologyOverFieldMap_actionOf_smul (p : ℕ) (n j : ℤ) (c : k)
    (s : twistSectionSpace k f L n) :
    (cohomologyOverFieldMap k f
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j (c • s)) p).hom =
      c • (cohomologyOverFieldMap k f
        (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) p).hom :=
  LinearMap.ext fun x => cohomologyOverFieldMap_actionOf_smul_apply k f L F p n j c s x

/-- **The `k`-linear action of the global sections of `L^{⊗ n}` on cohomology.** -/
def twistCohomologyAction (p : ℕ) (n j : ℤ) :
    twistSectionSpace k f L n →ₗ[k]
      (cohomologyOverField k f (TwistedGradedModule.twist X L F j) p →ₗ[k]
        cohomologyOverField k f (TwistedGradedModule.twist X L F (n + j)) p) where
  toFun s := (cohomologyOverFieldMap k f
    (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) p).hom
  map_add' s s' :=
    congrArg ModuleCat.Hom.hom (cohomologyOverFieldMap_actionOf_add k f L F p n j s s')
  map_smul' c s := cohomologyOverFieldMap_actionOf_smul k f L F p n j c s

/-- **Multiplication by two global sections of tensor powers commutes on cohomology over
`k`**, up to the maps induced by the reindexing comparisons of the twists. -/
theorem cohomologyOverFieldMap_actionOf_comm (p : ℕ) (n m j : ℤ)
    (s : twistSectionSpace k f L n) (t : twistSectionSpace k f L m)
    (h₁ : n + (m + j) = m + n + j) (h₂ : m + (n + j) = m + n + j) :
    cohomologyOverFieldMap k f (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F m j t) p ≫
        cohomologyOverFieldMap k f
            (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n (m + j) s) p ≫
          cohomologyOverFieldMap k f (TwistedGradedModule.reindexTwist X L F h₁) p =
      cohomologyOverFieldMap k f (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F n j s) p ≫
        cohomologyOverFieldMap k f
            (actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F m (n + j) t) p ≫
          cohomologyOverFieldMap k f (TwistedGradedModule.reindexTwist X L F h₂) p :=
  (cohomologyOverFieldMap_comp₃ k f p _ _ _).symm.trans
    ((congrArg (fun φ => cohomologyOverFieldMap k f φ p)
      (actionOf_comm (sectionSiteRing X) (sectionSiteSheaf X) L F n m j s t h₁ h₂)).trans
      (cohomologyOverFieldMap_comp₃ k f p _ _ _))

end Twist

end OverField

end Stacks.Cohomology.TwistCohomologyAction

end
