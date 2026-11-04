module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.ModuleMapBaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.AffineChartsAlongLimit
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackVanishing
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# A homomorphism of quasi-coherent modules on an affine chart

Let `u : F ⟶ G` be a homomorphism of quasi-coherent modules on a scheme `X` over `S`, and let `W`
be an affine open of `X`, identified with `Spec A`.  Over `W` the homomorphism is the associated
sheaf of a homomorphism of `A`-modules, namely of its module of global sections, and for every
`A`-algebra `R` the inverse image of `u` on `Spec R` is the associated sheaf of the extension of
scalars of that homomorphism along `A ⟶ R`.  In particular the inverse image of `u` on `Spec R`
vanishes exactly when that extension of scalars does, and the chart's module of global sections
is a finite `A`-module as soon as `F` is of finite type.

This is the chart-level dictionary which turns the conditions of
`Stacks.Flatness.ModuleMapBaseChangeSituation` into commutative algebra.

## Main definitions

* `Stacks.Flatness.ModuleMapBaseChangeSituation.chartInclusion` and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.chartHom` are the morphism `Spec A ⟶ X` given by
  an identification of an affine open with `Spec A`, and the inverse image of the situation's
  homomorphism along it.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.pullback_chartHom_eq_zero_iff` and
  `Stacks.Flatness.ModuleMapBaseChangeSituation.pullback_eq_zero_iff_of_factorsThrough_chart`
  translate vanishing of an inverse image into vanishing of an extension of scalars.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.module_finite_moduleSpecΓ_chart`: the chart's
  module of global sections is finite.

## Implementation notes

The translation is assembled from two naturality squares whose vertical maps are isomorphisms:
that of the counit `SheafOfModules.fromTildeΓ` of the associated-sheaf adjunction, which is an
isomorphism on quasi-coherent modules over an affine scheme, and that of the canonical
comparison `AlgebraicGeometry.pullbackTildeIso` between inverse image of an associated sheaf and
the associated sheaf of an extension of scalars (Stacks Tag 01I9).  Nothing depends on a choice
of presentation of the modules: both are natural transformations, so each square is an instance
of naturality.

## References

* [Stacks Project, Tag 05MH](https://stacks.math.columbia.edu/tag/05MH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace CategoryTheory

/-- In a square whose two vertical maps are isomorphisms, one horizontal map is an isomorphism
exactly when the other is. -/
theorem isIso_iff_of_sq_of_isIso {C : Type*} [Category C] {P Q Y Z : C} {a : P ⟶ Q}
    {b : Y ⟶ Z} {x : P ⟶ Y} {y : Q ⟶ Z} (ha : IsIso a) (hb : IsIso b) (h : a ≫ y = x ≫ b) :
    IsIso x ↔ IsIso y := by
  have := ha
  have := hb
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso (a ≫ y) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left a y
  · have : IsIso (x ≫ b) := by rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right x b

end CategoryTheory

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- In a square whose two vertical maps are isomorphisms, one horizontal map is zero exactly
when the other is. -/
private lemma eq_zero_iff_of_sq_of_isIso {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {W X Y Z : C} {a : W ⟶ X} {b : Y ⟶ Z} {x : W ⟶ Y} {y : X ⟶ Z} (ha : IsIso a) (hb : IsIso b)
    (h : a ≫ y = x ≫ b) : x = 0 ↔ y = 0 := by
  have := ha
  have := hb
  refine ⟨fun hx => (cancel_epi a).1 (h.trans ?_), fun hy => (cancel_mono b).1 ?_⟩
  · rw [hx, Limits.zero_comp, Limits.comp_zero]
  · rw [← h, hy, Limits.comp_zero, Limits.zero_comp]

variable (D : ModuleMapBaseChangeSituation.{u}) (W : D.X.Opens) (A R : CommRingCat.{u})
  (eW : (W : Scheme.{u}) ≅ Spec A) (f : A ⟶ R)

/-- The morphism `Spec A ⟶ X` given by an identification of an affine open `W` of `X` with
`Spec A`. -/
noncomputable abbrev chartInclusion : Spec A ⟶ D.X := eW.inv ≫ W.ι

/-- The inverse image on an affine chart of the homomorphism of quasi-coherent modules of the
situation. -/
noncomputable abbrev chartHom :
    (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F ⟶
      (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.G :=
  (Scheme.Modules.pullback (D.chartInclusion W A eW)).map D.hom

/-- **Vanishing of an inverse image of the chart homomorphism is vanishing of an extension of
scalars.**  For an `A`-algebra `R`, the inverse image of the chart homomorphism along the induced
morphism `Spec R ⟶ Spec A` is zero exactly when the extension of scalars to `R` of its module of
global sections is zero. -/
theorem pullback_chartHom_eq_zero_iff :
    letI : Algebra A R := f.hom.toAlgebra
    LinearMap.baseChange R (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom = 0 ↔
      (Scheme.Modules.pullback (Spec.map f)).map (D.chartHom W A eW) = 0 := by
  let _ : Algebra (A : Type u) (R : Type u) := f.hom.toAlgebra
  set F := (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F
  set G := (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.G
  set v := D.chartHom W A eW
  set P := Scheme.Modules.pullback (Spec.map f)
  set L := moduleSpecΓFunctor (R := A)
  have hisoF : IsIso (P.map F.fromTildeΓ) := inferInstance
  have hisoG : IsIso (P.map G.fromTildeΓ) := inferInstance
  have hnat₀ : F.fromTildeΓ ≫ v = (tilde.functor A).map (L.map v) ≫ G.fromTildeΓ :=
    ((Scheme.Modules.fromTildeΓNatTrans (R := A)).naturality (X := F) (Y := G) v).symm
  have hsq : P.map F.fromTildeΓ ≫ P.map v =
      P.map ((tilde.functor A).map (L.map v)) ≫ P.map G.fromTildeΓ :=
    (P.map_comp F.fromTildeΓ v).symm.trans
      ((congrArg P.map hnat₀).trans (P.map_comp _ _))
  have hstep₁ : P.map ((tilde.functor A).map (L.map v)) = 0 ↔ P.map v = 0 :=
    eq_zero_iff_of_sq_of_isIso hisoF hisoG hsq
  have hnat := (pullbackTildeIso A R f).hom.naturality (L.map v)
  have hstep₂ : P.map ((tilde.functor A).map (L.map v)) = 0 ↔
      (tilde.functor R).map ((ModuleCat.extendScalars f.hom).map (L.map v)) = 0 :=
    eq_zero_iff_of_sq_of_isIso inferInstance inferInstance hnat.symm
  have hfaithful : (tilde.functor R).Faithful :=
    inferInstanceAs ((AlgebraicGeometry.tildeEquiv (R := R)).functor ⋙
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι).Faithful
  have hstep₃ : (tilde.functor R).map ((ModuleCat.extendScalars f.hom).map (L.map v)) = 0 ↔
      (ModuleCat.extendScalars f.hom).map (L.map v) = 0 :=
    (tilde.functor R).map_eq_zero_iff
  have hstep₄ : (ModuleCat.extendScalars f.hom).map (L.map v) = 0 ↔
      LinearMap.baseChange R (L.map v).hom = 0 :=
    ⟨fun h => congrArg ModuleCat.Hom.hom h, fun h => ModuleCat.hom_ext h⟩
  rw [← hstep₄, ← hstep₃, ← hstep₂, hstep₁]

/-- **Vanishing of an inverse image along a morphism factoring through an affine chart.**  If a
morphism `Spec R ⟶ X` factors as the spectrum of `f : A ⟶ R` followed by the chart inclusion,
then the inverse image along it of the homomorphism of the situation is zero exactly when the
extension of scalars to `R` of the chart homomorphism's module of global sections is zero. -/
theorem pullback_eq_zero_iff_of_factorsThrough_chart {g : Spec R ⟶ D.X}
    (hg : g = Spec.map f ≫ D.chartInclusion W A eW) :
    letI : Algebra A R := f.hom.toAlgebra
    LinearMap.baseChange R (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom = 0 ↔
      (Scheme.Modules.pullback g).map D.hom = 0 := by
  calc _ ↔ (Scheme.Modules.pullback (Spec.map f)).map (D.chartHom W A eW) = 0 :=
        D.pullback_chartHom_eq_zero_iff W A R eW f
    _ ↔ (Scheme.Modules.pullback (Spec.map f ≫ D.chartInclusion W A eW)).map D.hom = 0 :=
        (Scheme.Modules.pullback_comp_map_eq_zero_iff _ _ D.hom).symm
    _ ↔ (Scheme.Modules.pullback g).map D.hom = 0 := by rw [hg]

/-- **The chart's module of global sections is finite.**  If the source module of the situation
is of finite type, then the module of global sections of its inverse image on an affine chart is
a finite module over the chart's coordinate ring. -/
theorem module_finite_moduleSpecΓ_chart [D.F.IsFiniteType] :
    Module.Finite (A : Type u) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F)) := by
  set F := (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F
  have hFft : F.IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (D.chartInclusion W A eW).toLRSHom.toShHom D.F
  exact (tilde_isFiniteType_iff _).mp
    (Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso F.fromTildeΓ).symm)

/-- **Invertibility of an inverse image of the chart homomorphism is bijectivity of an extension
of scalars.**  For an `A`-algebra `R`, the inverse image of the chart homomorphism along the
induced morphism `Spec R ⟶ Spec A` is an isomorphism exactly when the extension of scalars to
`R` of its module of global sections is bijective. -/
theorem pullback_chartHom_isIso_iff :
    letI : Algebra A R := f.hom.toAlgebra
    Function.Bijective (LinearMap.baseChange R (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom)
      ↔ IsIso ((Scheme.Modules.pullback (Spec.map f)).map (D.chartHom W A eW)) := by
  let _ : Algebra (A : Type u) (R : Type u) := f.hom.toAlgebra
  set F := (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F
  set G := (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.G
  set v := D.chartHom W A eW
  set P := Scheme.Modules.pullback (Spec.map f)
  set L := moduleSpecΓFunctor (R := A)
  have hisoF : IsIso (P.map F.fromTildeΓ) := inferInstance
  have hisoG : IsIso (P.map G.fromTildeΓ) := inferInstance
  have hnat₀ : F.fromTildeΓ ≫ v = (tilde.functor A).map (L.map v) ≫ G.fromTildeΓ :=
    ((Scheme.Modules.fromTildeΓNatTrans (R := A)).naturality (X := F) (Y := G) v).symm
  have hsq : P.map F.fromTildeΓ ≫ P.map v =
      P.map ((tilde.functor A).map (L.map v)) ≫ P.map G.fromTildeΓ :=
    (P.map_comp F.fromTildeΓ v).symm.trans
      ((congrArg P.map hnat₀).trans (P.map_comp _ _))
  have hstep₁ : IsIso (P.map ((tilde.functor A).map (L.map v))) ↔ IsIso (P.map v) :=
    isIso_iff_of_sq_of_isIso hisoF hisoG hsq
  have hnat := (pullbackTildeIso A R f).hom.naturality (L.map v)
  have hstep₂ : IsIso (P.map ((tilde.functor A).map (L.map v))) ↔
      IsIso ((tilde.functor R).map ((ModuleCat.extendScalars f.hom).map (L.map v))) :=
    isIso_iff_of_sq_of_isIso inferInstance inferInstance hnat.symm
  have hfull : (tilde.functor R).Full :=
    inferInstanceAs ((AlgebraicGeometry.tildeEquiv (R := R)).functor ⋙
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι).Full
  have hfaithful : (tilde.functor R).Faithful :=
    inferInstanceAs ((AlgebraicGeometry.tildeEquiv (R := R)).functor ⋙
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι).Faithful
  have hstep₃ : IsIso ((tilde.functor R).map ((ModuleCat.extendScalars f.hom).map (L.map v))) ↔
      IsIso ((ModuleCat.extendScalars f.hom).map (L.map v)) :=
    isIso_iff_of_reflects_iso _ (tilde.functor R)
  have hstep₄ : IsIso ((ModuleCat.extendScalars f.hom).map (L.map v)) ↔
      Function.Bijective (LinearMap.baseChange R (L.map v).hom) :=
    ConcreteCategory.isIso_iff_bijective _
  rw [← hstep₄, ← hstep₃, ← hstep₂, hstep₁]

/-- **The chart's module of global sections of the target is finitely presented.**  If the
target module of the situation is of finite presentation, then the module of global sections of
its inverse image on an affine chart is a finitely presented module over the chart's coordinate
ring. -/
theorem module_finitePresentation_moduleSpecΓ_chart [D.G.IsFinitePresentation] :
    Module.FinitePresentation (A : Type u) (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.G)) := by
  set G := (Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.G
  have hGfp : G.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (D.chartInclusion W A eW).toLRSHom.toShHom D.G ‹_›
  exact (tilde_isFinitePresentation_iff _).mp
    ((SheafOfModules.isFinitePresentation.{u, u, u} _).prop_of_iso
      (asIso G.fromTildeΓ).symm hGfp)

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
