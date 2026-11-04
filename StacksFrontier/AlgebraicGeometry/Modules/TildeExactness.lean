module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Exactness of the affine associated-sheaf functor

For a commutative ring `R`, the functor `M ↦ M̃` from `R`-modules to sheaves of modules on
`Spec R` is exact. Right exactness is already available: the functor is a left adjoint, by the
adjunction with global sections. This file supplies the other half, preservation of finite
limits.

## Main results

* `AlgebraicGeometry.tilde.preservesFiniteLimits`: the functor `M ↦ M̃` preserves finite limits.

## Implementation notes

The codomain of `AlgebraicGeometry.tilde.functor` is `(Spec R).Modules`, which is a
non-reducible definition wrapping `SheafOfModules (Spec R).ringCatSheaf`. The stalkwise
exactness criterion is stated for the latter, so the functor is reinterpreted there before the
criterion is applied.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.tilde

/-- The associated-sheaf functor, read in the category of sheaves of modules over the structure
sheaf of `Spec R` rather than in the definitionally equal `(Spec R).Modules`. -/
private noncomputable abbrev sheafOfModulesFunctor (R : CommRingCat.{u}) :
    ModuleCat.{u} R ⥤ SheafOfModules.{u} (Spec R).ringCatSheaf := tilde.functor R

private instance sheafOfModulesFunctorAdditive (R : CommRingCat.{u}) :
    (sheafOfModulesFunctor R).Additive where
  map_add := by
    intro X Y f g
    change tilde.map (f + g) = tilde.map f + tilde.map g
    exact tilde.map_add f g

/-- The functor associating to an `R`-module the sheaf `M̃` on `Spec R` preserves finite limits.
Together with its left-adjointness this is its exactness. -/
instance preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R) := by
  have hExact : ∀ (S : ShortComplex (ModuleCat.{u} R)), S.Exact →
      (S.map (sheafOfModulesFunctor R)).Exact := by
    intro S hS
    apply (SheafOfModules.exact_iff_stalkShortComplex_exact (Spec R).ringCatSheaf
      (S.map (sheafOfModulesFunctor R))).2
    intro x
    let y : PrimeSpectrum.Top R := x
    change (SheafOfModules.stalkShortComplex (Spec R).ringCatSheaf
      (S.map (sheafOfModulesFunctor R)) y).Exact
    let U := SheafOfModules.stalkShortComplex (Spec R).ringCatSheaf
      (S.map (sheafOfModulesFunctor R)) y
    have : y.asIdeal.IsPrime := y.isPrime
    let f₁ := (tilde.toStalk S.X₁ y).hom
    let f₂ := (tilde.toStalk S.X₂ y).hom
    let f₃ := (tilde.toStalk S.X₃ y).hom
    have hex : Function.Exact
        (IsLocalizedModule.map y.asIdeal.primeCompl f₁ f₂ S.f.hom)
        (IsLocalizedModule.map y.asIdeal.primeCompl f₂ f₃ S.g.hom) :=
      IsLocalizedModule.map_exact y.asIdeal.primeCompl f₁ f₂ f₃ S.f.hom S.g.hom
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)
    have hf : (U.f : U.X₁ → U.X₂) = fun m ↦
        IsLocalizedModule.map y.asIdeal.primeCompl f₁ f₂ S.f.hom m := by
      funext m
      change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (Scheme.Modules.Hom.mapPresheaf (tilde.map S.f))) m = _
      exact tilde.toStalk_map S.f y m
    have hg : (U.g : U.X₂ → U.X₃) = fun m ↦
        IsLocalizedModule.map y.asIdeal.primeCompl f₂ f₃ S.g.hom m := by
      funext m
      change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (Scheme.Modules.Hom.mapPresheaf (tilde.map S.g))) m = _
      exact tilde.toStalk_map S.g y m
    apply (ShortComplex.ab_exact_iff_function_exact U).2
    intro m
    constructor
    · intro hm
      obtain ⟨n, hn⟩ := (hex m).mp ((congrFun hg m).symm.trans hm)
      exact ⟨n, (congrFun hf n).trans hn⟩
    · rintro ⟨n, rfl⟩
      simp
  have hlim := ((Functor.exact_tfae (sheafOfModulesFunctor R)).out 2 4).mp hExact
  exact hlim.1

end AlgebraicGeometry.tilde
