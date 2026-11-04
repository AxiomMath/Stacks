module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.EssentialSurjectivity
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent.EssentialSurjectivity

/-!
# Stacks 0A0X under the cutoff bound, with Stacks 07SK discharged

The assembly of Stacks 0A0X under the cutoff bound, with its hypothesis on Stacks 07SK discharged
by the essential surjectivity
`AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation` of the
`EssentialSurjectivity` part of this split.

## Main results

* `AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_wSystems` and
  `AlgebraicGeometry.Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_wSystems`: the
  assembly of Stacks 0A0X under the cutoff bound and its form for Stacks 0D3D, with the hypothesis
  on Stacks 07SK discharged.

Nothing here is registered: Stacks 07SK is registered on the forms bounded by the cofinality.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-! ### The assembly of Stacks 0A0X with Stacks 07SK discharged -/

section Assembly

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

open Opposite

/-- Stacks 07SK for cutoff bounded systems, in the form of the hypothesis `h07SK` of the
assemblies below. -/
private theorem exists_model_of_finitePresentation_aux :
    ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ) :=
  fun {_} _ _ D hC hD hA hQc hQs Y hY hFp =>
    IsCutoffBoundedSystem.exists_model_of_finitePresentation B _ hZ hZ D hD hA hQc hQs hC Y hY hFp

/-- **Stacks 0A0X, from the approximations it is proved with, under the cutoff bound, with
Stacks 07SK discharged.** This is
`exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedApproximations` with its
hypothesis `h07SK` discharged by `IsCutoffBoundedSystem.exists_model_of_finitePresentation`. The
remaining hypotheses are the inputs still owed: Stacks 07SU (`hW`, and `hconv` for the convention
on its approximation), Stacks 0A0W (`h0A0W`) and Stacks 08K1 under the convention (`h08K1`). -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_wSystems
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder;
        IsCutoffBoundedSystem B _ hZ A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) :=
  exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedApproximations hZ hW hconv
    h0A0W
    (exists_model_of_finitePresentation_aux hZ)
    h08K1 hX hY f hf hYqc hYqs

/-- **Stacks 0A0X over an affine target, in the shape the assembly of Stacks 0D3D consumes,
under the cutoff bound, with Stacks 07SK discharged.** This is
`AlgebraicGeometry.Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_approximations`
with its hypothesis `h07SK` discharged by
`AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_model_of_finitePresentation`. The
remaining hypotheses `hW`, `hconv`, `h0A0W` and `h08K1` are the inputs still owed. -/
theorem exists_descentSituation_arrow_isCutoffBoundedSystem_of_wSystems
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder;
        IsCutoffBoundedSystem B _ hZ A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        IsCutoffBoundedSystem B _ hZ DX.system ∧ IsCutoffBoundedSystem B _ hZ DY.system :=
  exists_descentSituation_arrow_isCutoffBoundedSystem_of_approximations hZ hW hconv h0A0W
    (exists_model_of_finitePresentation_aux hZ)
    h08K1

end Assembly

end AlgebraicGeometry.Space

end
