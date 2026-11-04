module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantNorm
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# A finite locally free cover is of finite presentation, as a module and as a sheaf

Let `p : W ⟶ T` be a finite locally free morphism of schemes. Over an affine target, the global
functions on `W` are a finitely presented module over the global functions on `T`; and the direct
image `p_* 𝒪_W` is a sheaf of modules of finite presentation on `T`, with no hypothesis on `T`.

## Main results

* `AlgebraicGeometry.finitePresentation_appTop_of_isFiniteLocallyFree`: over an affine target,
  `Γ(W, 𝒪_W)` is a finitely presented `Γ(T, 𝒪_T)`-module.
* `AlgebraicGeometry.isFinitePresentation_pushforwardStructureSheaf`: `p_* 𝒪_W` is a sheaf of
  modules of finite presentation.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For `p : W ⟶ T` finite locally free with `T` affine, `Γ(W, 𝒪_W)` is a finitely presented
module over `Γ(T, 𝒪_T)` for the algebra structure induced by `p`. -/
public theorem finitePresentation_appTop_of_isFiniteLocallyFree {W T : Scheme.{u}} (p : W ⟶ T)
    [IsAffine T] [Stacks.Morphisms.IsFiniteLocallyFree p] :
    letI := p.appTop.hom.toAlgebra
    Module.FinitePresentation Γ(T, ⊤) Γ(W, ⊤) := by
  let : Algebra Γ(T, ⊤) Γ(W, ⊤) := p.appTop.hom.toAlgebra
  obtain ⟨hfin, hproj⟩ :=
    AlgebraicGeometry.GroupoidScheme.finite_projective_appTop_of_isFiniteLocallyFree p
  have := hfin
  have := hproj
  exact Module.finitePresentation_of_projective _ _

/-- For `p : W ⟶ T` finite locally free, the direct image `p_* 𝒪_W` of the structure sheaf is a
sheaf of modules of finite presentation. -/
public theorem isFinitePresentation_pushforwardStructureSheaf {W T : Scheme.{u}} (p : W ⟶ T)
    [Stacks.Morphisms.IsFiniteLocallyFree p] :
    (Stacks.Morphisms.pushforwardStructureSheaf p).IsFinitePresentation :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation _
    ((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators _).mp
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_pointwise p).mp inferInstance).2)

end AlgebraicGeometry

end
