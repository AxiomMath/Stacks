module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Hyperplane
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneDegreeOneSurjective

/-!
# Restricting global sections along an isomorphism of schemes

For an isomorphism of schemes `i : P ⟶ Q` and a module `N` on `Q`, restriction of global sections
`AlgebraicGeometry.pullbackGlobalSections i N : Γ(N, ⊤) ⟶ Γ(i^*N, ⊤)` is bijective. A left
inverse is restriction along `inv i`, read through the identification `(inv i)^* i^* N ≅ N`.

## Main results

* `Stacks.AmpleFibreNeighbourhood.injective_pullbackGlobalSections_of_isIso`: restriction of
  global sections along an isomorphism of schemes is injective.
* `Stacks.AmpleFibreNeighbourhood.bijective_pullbackGlobalSections_of_isIso`: restriction of
  global sections along an isomorphism of schemes is bijective.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- For an isomorphism of schemes `i : P ⟶ Q` and a module `N` on `Q`, restriction of global
sections `AlgebraicGeometry.pullbackGlobalSections i N : Γ(N, ⊤) ⟶ Γ(i^*N, ⊤)` is injective. -/
theorem injective_pullbackGlobalSections_of_isIso {P Q : Scheme.{u}} (i : P ⟶ Q) [IsIso i]
    (N : Q.Modules) :
    Function.Injective fun x : Γ(N, ⊤) => pullbackGlobalSections i N x := by
  intro s t h
  have hcomp := congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp (inv i) i).hom.app N) ⊤
      (pullbackGlobalSections (inv i) ((Scheme.Modules.pullback i).obj N) z)) h
  rw [SectionsEqualizer.pullbackGlobalSections_comp,
    SectionsEqualizer.pullbackGlobalSections_comp] at hcomp
  have hcongr := congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id i)).hom.app N) ⊤ z) hcomp
  rw [SectionsEqualizer.pullbackGlobalSections_congr,
    SectionsEqualizer.pullbackGlobalSections_congr] at hcongr
  have hid := congrArg
    (fun z => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId Q).hom.app N) ⊤ z) hcongr
  simpa only [Stacks.Chow.FreeTower.pullbackGlobalSections_id] using hid

/-- For an isomorphism of schemes `i : P ⟶ Q` and a module `N` on `Q`, restriction of global
sections `AlgebraicGeometry.pullbackGlobalSections i N : Γ(N, ⊤) ⟶ Γ(i^*N, ⊤)` is bijective. -/
theorem bijective_pullbackGlobalSections_of_isIso {P Q : Scheme.{u}} (i : P ⟶ Q) [IsIso i]
    (N : Q.Modules) :
    Function.Bijective fun x : Γ(N, ⊤) => pullbackGlobalSections i N x :=
  ⟨injective_pullbackGlobalSections_of_isIso i N,
    surjective_pullbackGlobalSections_of_isIso i N⟩

end Stacks.AmpleFibreNeighbourhood

end
