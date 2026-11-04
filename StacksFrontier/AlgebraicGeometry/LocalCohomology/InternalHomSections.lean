module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.SchemeQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of the sheaf-hom over an open are the morphisms over that open

Let `X` be a scheme, let `G` and `F` be `𝒪_X`-modules and let `U` be an open of `X`. The sections
over `U` of the sheaf-hom `Hom(G, F)`,
`Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheaf`, are the morphisms `G|_U ⟶ F|_U` of
sheaves of modules on the slice site `Over U`. This module identifies them with the morphisms
`G|_U ⟶ F|_U` of `𝒪_U`-modules on the open subscheme `U`, the restriction being
`AlgebraicGeometry.Scheme.Modules.restrict`.

## Main definitions

* `Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheafSectionsEquiv`: the bijection
  `Γ(Hom(G, F), U) ≃ (G|_U ⟶ F|_U)`.

## Main results

* `Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheafSectionsEquiv_apply`: the morphism
  attached to a section `s` acts on sections over an open `W` of `U` exactly as `s` acts at the
  object of `Over U` that `W` corresponds to under `TopologicalSpace.Opens.overEquivalence`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom

universe u

namespace Stacks.AlgebraicGeometry.InternalHomScheme

variable {X : Scheme.{u}}

/-- The sections of the sheaf-hom `internalHomSheaf G F` over an open `U` are the `𝒪_U`-linear
maps `G|_U ⟶ F|_U` on the open subscheme `U`, the restriction being
`AlgebraicGeometry.Scheme.Modules.restrict`. -/
@[ega "0 4.1.5" "schemes"]
public noncomputable def internalHomSheafSectionsEquiv (G F : X.Modules) (U : X.Opens) :
    Γ(internalHomSheaf G F, U) ≃ (G.restrict U.ι ⟶ F.restrict U.ι) :=
  ((SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).homEquiv
      (X := SheafOfModules.over G U) (Y := SheafOfModules.over F U)).symm.trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app G)
        ((Scheme.Modules.overFunctorEquiv U).app F)))

/-- The morphism `G|_U ⟶ F|_U` attached by `internalHomSheafSectionsEquiv` to a section `s` of
`Hom(G, F)` over `U` acts on the sections over an open `W` of `U`, which are the sections of `G`
over `U.ι ''ᵁ W`, exactly as `s` acts at the object of `Over U` corresponding to `W`. -/
public lemma internalHomSheafSectionsEquiv_apply (G F : X.Modules) (U : X.Opens)
    (s : Γ(internalHomSheaf G F, U)) (W : U.toScheme.Opens) (x : Γ(G, U.ι ''ᵁ W)) :
    (internalHomSheafSectionsEquiv G F U s).val.app (op W) x =
      s.app (op (U.overEquivalence.inverse.obj W)) x :=
  rfl

end Stacks.AlgebraicGeometry.InternalHomScheme

end
