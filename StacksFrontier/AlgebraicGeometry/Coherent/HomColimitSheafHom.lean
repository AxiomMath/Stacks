module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent

/-!
# The ideal-power Hom colimit of a sheaf Hom

Let `X` be a Noetherian scheme, let `I` be a quasi-coherent sheaf of ideals, let `U` be the
complement of the closed subscheme it cuts out, let `G` be an `𝒪_X`-module of finite
presentation and let `F` be a quasi-coherent `𝒪_X`-module.  Applying the global-sections clause
of [Stacks, Tag 01YB] to the sheaf `H = SheafHom_{𝒪_X}(G, F)`, which is quasi-coherent, gives a
bijection

`colim_n Hom_{𝒪_X}(Iⁿ, SheafHom_{𝒪_X}(G, F)) ⟶ Γ(SheafHom_{𝒪_X}(G, F), U)`

whose target is, by the definition of the internal Hom, the morphisms `G|_U ⟶ F|_U` on the
slice site over `U`.

This is the opening step of the Stacks Project's proof of the *first* display of Tag 01YB,
`colim_n Hom_{𝒪_X}(Iⁿ G, F) ≅ Hom_{𝒪_U}(G|_U, F|_U)`; it is not that display, and no clause of
Tag 01YB is claimed here.  What lies between the two is the comparison of `Iⁿ ⊗ G` with the
submodule `Iⁿ G`: the tensor-hom correspondence turns a map `Iⁿ ⟶ SheafHom(G, F)` into a map
`Iⁿ ⊗_{𝒪_X} G ⟶ F`, and Artin-Rees is then used again to see that, after increasing `n`, the
natural map `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m}G` is an isomorphism.  That comparison is carried out in
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/FirstDisplaySurjectivity.lean`, where the
display is proved.

## Main definitions

* `sectionsSheafHomModulesEquiv`: the sections of `SheafHom_{𝒪_X}(G, F)` over an open `U` are
  the morphisms `G|_U ⟶ F|_U` of modules on the slice site over `U`.  This is the
  identification the source makes with the words "by definition".

## Main results

* `canonicalMapToSections_sheafHomModules_bijective`: the global-sections clause of Tag 01YB
  applied to `SheafHom_{𝒪_X}(G, F)`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPowerColimit

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.InternalHomModules

variable {X : Scheme.{u}}

/-- **The global-sections clause of Stacks, Tag 01YB applied to a sheaf Hom.**  For `G` of
finite presentation and `F` quasi-coherent on a Noetherian scheme, the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, SheafHom_{𝒪_X}(G, F)) ⟶ Γ(SheafHom_{𝒪_X}(G, F), U)`

is a bijection, because `SheafHom_{𝒪_X}(G, F)` is quasi-coherent. -/
public theorem canonicalMapToSections_sheafHomModules_bijective
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (G F : X.Modules)
    (hG : G.IsFinitePresentation) [F.IsQuasicoherent] :
    Function.Bijective (canonicalMapToSections I (sheafHomModules G F)) :=
  have := isQuasicoherent_sheafHomModules G F hG
  canonicalMapToSections_bijective_of_isQuasicoherent I (sheafHomModules G F)

/-- **The sections of the sheaf Hom over an open `U` are the morphisms `F|_U ⟶ H|_U`** of
modules over `𝒪_X.over U` on the slice site over `U`.

Both sides are the morphisms of the underlying presheaves of modules of the restrictions, so
the bijection only adds and removes the one-field wrapper of `SheafOfModules.Hom`. -/
public def sectionsSheafHomModulesEquiv (F H : X.Modules) (U : X.Opens) :
    Γ(sheafHomModules F H, U) ≃ (F.over U ⟶ H.over U) where
  toFun t := { val := t }
  invFun f := f.val
  left_inv _ := rfl
  right_inv _ := rfl

end Stacks.AlgebraicGeometry.InternalHomModules

end

end
