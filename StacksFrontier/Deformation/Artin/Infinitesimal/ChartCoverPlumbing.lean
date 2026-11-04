module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartTangentFunctor
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentBaseChangeDescent

/-!
# Charts over `Spec A` and rows of tangent modules

Two pieces of bookkeeping for the reduction of Stacks 0DNT to chart points.

* **Charts over `Spec A`.** For `T' = Spec A` as an object of the site
  (`Deformation.Artin.algebraOver`), `A' = Γ(T', ⊤)` is `A` up to `Scheme.ΓSpecIso`. A small
  `A'`-algebra `X` is an `A`-algebra through `A → A'` (`Deformation.Artin.ChartLift.baseAlgebra`),
  and the structure morphism of `Spec X` through `Spec A` is the structure morphism `toSOf X` of
  the chart (`Deformation.Artin.ChartLift.specMap_comp_toS_eq_toSOf`). So a chart point over `X` is
  an object over `algebraOver X.obj` for the ring map `A → X`, as the descent of
  `Deformation.Artin.isTangentBaseChangeIso_of_equalizer` needs.
* **Rows.** The rows of tangent modules of `Deformation.Artin.isTangentBaseChangeIso_of_equalizer`
  are exact as soon as the corresponding rows of classes of lifts are
  (`Deformation.Artin.rowExact_of_liftClassRowExact`): the maps of Stacks 07YA are the pullbacks
  of lift classes read through the identifications of the tangent functors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Stack.GroupoidLift AlgebraicGeometry.Space.ChartDescent

namespace Deformation.Artin

universe u v w

section Rows

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  {A A₁ A₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂]
  {f₀₁ : A →+* A₁} {a b : A₁ →+* A₂}
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of A₂) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of A₂))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom f₀₁) ≫ toS = toS₁}
  {hfa : Spec.map (CommRingCat.ofHom a) ≫ toS₁ = toS₂}
  {hfb : Spec.map (CommRingCat.ofHom b) ≫ toS₁ = toS₂}
  {x x₁ x₂ : X}
  {hx : p.obj x = algebraOver A B S hS toS hA} {hx₁ : p.obj x₁ = algebraOver A₁ B S hS toS₁ hA₁}
  {hx₂ : p.obj x₂ = algebraOver A₂ B S hS toS₂ hA₂}
  {φ₀₁ : x₁ ⟶ x}
  {hφ₀₁ : p.IsHomLift (algebraOverMapOfRingHom f₀₁ B S hS toS toS₁ hA hA₁ hf₀₁) φ₀₁}
  {α β : x₂ ⟶ x₁}
  {hα : p.IsHomLift (algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa) α}
  {hβ : p.IsHomLift (algebraOverMapOfRingHom b B S hS toS₁ toS₂ hA₁ hA₂ hfb) β}
  {M : SiteModule A B} {M₁ : SiteModule A₁ B} {M₂ : SiteModule A₂ B}
  {ψ₀₁ : M.obj ⟶ (ModuleCat.restrictScalars f₀₁).obj M₁.obj}
  {ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj}
  {ψb : M₁.obj ⟶ (ModuleCat.restrictScalars b).obj M₂.obj}

include hx hx₁ hx₂ in
variable (hφ₀₁ hα hβ ψ₀₁ ψa ψb) in
/-- **The row of lift classes is exact**: the pullback of lift classes along `A[M] → A₁[M₁]` is
injective with image the equalizer of the two pullbacks along `A₁[M₁] ⇉ A₂[M₂]`. This is the
sheaf condition of the functor of Stacks 0DNS for the covering `A[M] → A₁[M₁]`. -/
def LiftClassRowExact : Prop :=
  Function.Injective (liftClassPullback f₀₁ hf₀₁ hp φ₀₁ hφ₀₁ (hx := hx) (hy := hx₁) ψ₀₁) ∧
    ∀ c₁ : squareZeroLiftClasses A₁ B S hS toS₁ hA₁ p x₁ hx₁ M₁,
      (liftClassPullback a hfa hp α hα (hx := hx₁) (hy := hx₂) ψa c₁ =
          liftClassPullback b hfb hp β hβ (hx := hx₁) (hy := hx₂) ψb c₁ ↔
        ∃ c, liftClassPullback f₀₁ hf₀₁ hp φ₀₁ hφ₀₁ (hx := hx) (hy := hx₁) ψ₀₁ c = c₁)

include hp in
/-- **Exact rows of lift classes give exact rows of tangent modules**, for any realizations of
the tangent functors. -/
theorem rowExact_of_liftClassRowExact
    (F : TangentFunctorData A B S hS toS hA p x hx)
    (F₁ : TangentFunctorData A₁ B S hS toS₁ hA₁ p x₁ hx₁)
    (F₂ : TangentFunctorData A₂ B S hS toS₂ hA₂ p x₂ hx₂)
    (h : LiftClassRowExact hp hφ₀₁ hα hβ ψ₀₁ ψa ψb (hx := hx) (hx₁ := hx₁) (hx₂ := hx₂)) :
    Function.Injective (tangentPullbackFun f₀₁ hf₀₁ hp φ₀₁ hφ₀₁ F F₁ ψ₀₁) ∧
      ∀ t₁, (tangentPullbackFun a hfa hp α hα F₁ F₂ ψa t₁ =
          tangentPullbackFun b hfb hp β hβ F₁ F₂ ψb t₁ ↔
        ∃ t, tangentPullbackFun f₀₁ hf₀₁ hp φ₀₁ hφ₀₁ F F₁ ψ₀₁ t = t₁) := by
  have e₀ := liftEquiv_tangentPullbackFun f₀₁ hf₀₁ hp φ₀₁ hφ₀₁ F F₁ ψ₀₁
  have ea := liftEquiv_tangentPullbackFun a hfa hp α hα F₁ F₂ ψa
  have eb := liftEquiv_tangentPullbackFun b hfb hp β hβ F₁ F₂ ψb
  refine ⟨fun t t' htt ↦ (F.liftEquiv M).injective (h.1 ?_), fun t₁ ↦ ?_⟩
  · rw [← e₀, ← e₀, htt]
  · constructor
    · intro hab
      obtain ⟨c, hc⟩ := (h.2 (F₁.liftEquiv M₁ t₁)).1 (by
        rw [← ea, ← eb, hab])
      refine ⟨(F.liftEquiv M).symm c, (F₁.liftEquiv M₁).injective ?_⟩
      rw [e₀, Equiv.apply_symm_apply, hc]
    · rintro ⟨t, rfl⟩
      refine (F₂.liftEquiv M₂).injective ?_
      rw [ea, eb, e₀]
      exact (h.2 _).2 ⟨_, rfl⟩

end Rows

namespace ChartLift

section Base

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (A : Type u) [CommRing A]
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- The scheme underlying the site object `algebraOver A B S hS toS hA` is affine: it is
`Spec A`. -/
instance isAffine_algebraOver :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (algebraOver A B S hS toS hA)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

/-- The ring map `A → Γ(Spec A, ⊤)`. -/
abbrev toRingOf : A →+* ringOf B S hS (algebraOver A B S hS toS hA) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

variable {A toS hA}

/-- A small algebra over `Γ(Spec A, ⊤)` as an `A`-algebra. -/
abbrev baseAlgebra (X : SmallAlg (ringOf B S hS (algebraOver A B S hS toS hA)) B.cutoff) :
    Algebra A X.obj :=
  ((algebraMap (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj).comp
    (toRingOf A toS hA)).toAlgebra

/-- **The structure morphism of a chart point over `Spec A`**: `Spec X → Spec A → S` is the
structure morphism of `Spec X` in the chart. -/
theorem specMap_comp_toS_eq_toSOf
    (X : SmallAlg (ringOf B S hS (algebraOver A B S hS toS hA)) B.cutoff) :
    Spec.map (CommRingCat.ofHom ((algebraMap (ringOf B S hS (algebraOver A B S hS toS hA))
      X.obj).comp (toRingOf A toS hA))) ≫ toS = toSOf X := by
  have h1 : ((BigFppfOver.toScheme B S hS).obj (algebraOver A B S hS toS hA)).isoSpec.inv =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
    Scheme.isoSpec_Spec_inv (CommRingCat.of A)
  simp only [toSOf, specToBase, h1]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

end Base

end ChartLift

end Deformation.Artin

end
