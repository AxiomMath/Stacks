module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.Globalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic

/-!
# Sections over an affine chart of a complex flat over the base

Let `f : X ⟶ S` be a morphism of schemes, `U ⊆ X` and `V ⊆ S` affine opens with `f(U) ⊆ V`, and
`G` a bounded above complex of quasi-coherent `𝒪_X`-modules flat over `S`. Then the complex of
global sections of the pullback of `G` to `Spec 𝒪_X(U)` is a bounded above complex of flat
`𝒪_S(V)`-modules, hence K-flat over `𝒪_S(V)`.

## Main results

* `AlgebraicGeometry.flat_sections_pullback_fromSpec`: for `F` quasi-coherent and flat over `S`,
  the sections of the pullback of `F` to `Spec 𝒪_X(U)` form a flat `𝒪_S(V)`-module.
* `AlgebraicGeometry.kFlat_sectionsComplex_pullback_fromSpec`: the complex of sections over
  `Spec 𝒪_X(U)` of the pullback of `G` is K-flat over `𝒪_S(V)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For affine opens `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V` and a quasi-coherent `𝒪_X`-module `F`
flat over `S`, the global sections of the pullback of `F` to `Spec 𝒪_X(U)` form a flat
`𝒪_S(V)`-module. -/
theorem flat_sections_pullback_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) (F : X.Modules) [F.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    Module.Flat Γ(S, V) ((ModuleCat.restrictScalars (f.appLE V U hUV).hom).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj F))) := by
  have := hU.isOpenImmersion_fromSpec
  have hcrit := ((isFlatOver_tfae f F).out 1 2).mp hF
  let E : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback hU.fromSpec).obj F) ≅
      ModuleCat.of Γ(X, U) Γ(F, U) :=
    moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app F).symm ≪≫
        (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F) ≪≫
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections F ⟨U, hU⟩
  let : Module Γ(S, V) Γ(F, U) := Module.compHom Γ(F, U) (f.appLE V U hUV).hom
  exact @Module.Flat.of_linearEquiv Γ(S, V) _ _ _ _ _ _ _ (hcrit U hU V hV hUV)
    ((ModuleCat.restrictScalars (f.appLE V U hUV).hom).mapIso E).toLinearEquiv

/-- For affine opens `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V` and a bounded above complex `G` of
quasi-coherent `𝒪_X`-modules flat over `S`, the complex of global sections of the pullback of `G`
to `Spec 𝒪_X(U)` is K-flat over `𝒪_S(V)`. -/
theorem kFlat_sectionsComplex_pullback_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) (G : CochainComplex X.Modules ℤ)
    (hGminus : CochainComplex.minus X.Modules G) (hGq : ∀ n, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n, IsFlatOver f.toLRSHom.toShHom (G.X n)) :
    ((CochainComplex.restrictScalars (f.appLE V U hUV).hom).obj
      (sectionsComplex (((Scheme.Modules.pullback hU.fromSpec).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G))).KFlat := by
  obtain ⟨d, hd⟩ := (CochainComplex.minus_iff G).1 hGminus
  have hflat : ∀ n : ℤ, Module.Flat Γ(S, V)
      (((CochainComplex.restrictScalars (f.appLE V U hUV).hom).obj
        (sectionsComplex (((Scheme.Modules.pullback hU.fromSpec).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G))).X n) := fun n ↦
    have := hGq n
    flat_sections_pullback_fromSpec f hU hV hUV (G.X n) (hGflat n)
  have hle : ((CochainComplex.restrictScalars (f.appLE V U hUV).hom).obj
      (sectionsComplex (((Scheme.Modules.pullback hU.fromSpec).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G))).IsStrictlyLE d :=
    (CochainComplex.isStrictlyLE_iff _ d).2 fun i hi ↦
      Functor.map_isZero (ModuleCat.restrictScalars (f.appLE V U hUV).hom)
        (Functor.map_isZero (moduleSpecΓFunctor (R := Γ(X, U)))
          (Functor.map_isZero (Scheme.Modules.pullback hU.fromSpec)
            ((CochainComplex.isStrictlyLE_iff G d).1 hd i hi)))
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} _ d

end AlgebraicGeometry
