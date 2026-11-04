module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiRingedTopos
public import StacksFrontier.Topology.Simplicial.ComponentSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of modules on the Zariski ringed topos of a simplicial scheme, and components

For a morphism `f : V ⟶ U` of simplicial schemes the morphism of Zariski ringed topoi of
Stacks 07TI has a direct image on sheaves of modules, right adjoint to the pullback `f^*`.
In each simplicial degree a sheaf of `𝒪_X`-modules on the total Zariski site restricts to a
sheaf of modules on the scheme `X_n`, because the inclusion of the degree-`n` open-set site is
continuous and the degree-`n` component of `𝒪_X` is the structure sheaf of `X_n`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.modulePushforward`: the direct image `f_*` of sheaves of
  modules along a morphism of simplicial schemes.
* `AlgebraicGeometry.SimplicialScheme.componentStructureHom`: the degree-`n` component of the
  structure sheaf of the total Zariski site, read as a morphism to the direct image of `𝒪_X`
  along the inclusion of the component site.
* `AlgebraicGeometry.SimplicialScheme.componentModule`: the degree-`n` component `F_n` of a
  sheaf of `𝒪_X`-modules on the total Zariski site, a sheaf of modules on the scheme `X_n`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.modulePullbackAdjModulePushforward`: **Stacks 03D7 for a
  morphism of simplicial schemes.** Pullback is left adjoint to pushforward on the Zariski
  ringed topoi.
* `AlgebraicGeometry.SimplicialScheme.componentModule_obj_obj` and
  `AlgebraicGeometry.SimplicialScheme.modulePushforward_obj_obj`: the sections of a component
  and of a direct image, over an open of a single simplicial degree.

## Implementation notes

The direct image is the one of Stacks 03D6 for the morphism of ringed topoi
`AlgebraicGeometry.SimplicialScheme.zariskiRingedToposHom` of Stacks 07TI, so it is built the
same way as the pullback `modulePullback` there and inherits the adjunction of Stacks 03D7
from it.

The component in degree `n` is the restriction of a sheaf of modules along the inclusion
`levelFunctor` of the open-set site of `X_n` into the total Zariski site, which is a continuous
functor by Stacks 09W0; restriction of sheaves of modules along a continuous functor is
Mathlib's `SheafOfModules.pushforward`, and the morphism of sheaves of rings it needs is the
identification `structureComponentIso` of Stacks 07TI of the degree-`n` component of `𝒪_X` with
the structure sheaf of `X_n`. The component therefore lands in `(X.obj n).Modules` on the nose,
which is the shape the scheme-level results about quasi-coherence are stated in, and its
sections over an open `W` of `X_n` are the sections of the original module over the object
`(n, W)` of the total site, by `rfl`.

The topologies of the two sites are spelled in `componentStructureHom` and `componentModule`
through `zariskiSpace` rather than through the ringed topos, and the site functor of
`componentModule` is supplied explicitly: the continuity instance is indexed by the two
topologies, and the projection `(zariskiRingedTopos X).J` is not reducible, so the instance is
not found when the topology is presented in that form.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- Pushforward of sheaves of modules along a morphism of simplicial schemes: the direct image
on the total Zariski site, with the `𝒪_U`-action restricted along `f♯`. -/
public noncomputable def modulePushforward (f : V ⟶ U) : Modules V ⥤ Modules U :=
  Stacks.Sheaves.RingedToposModules.pushforwardModules
    (X := zariskiRingedTopos V) (Y := zariskiRingedTopos U)
    (zariskiRingedToposHom f).toRingedToposModulesHom

/-- **Stacks 03D7 for a morphism of simplicial schemes.** On the Zariski ringed topoi of
simplicial schemes the pullback of sheaves of modules is left adjoint to the pushforward. -/
public noncomputable def modulePullbackAdjModulePushforward (f : V ⟶ U) :
    modulePullback f ⊣ modulePushforward f :=
  Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (X := zariskiRingedTopos V) (Y := zariskiRingedTopos U)
    (zariskiRingedToposHom f).toRingedToposModulesHom

/-- The sections of a direct image over an open of a single simplicial degree are the sections
of the original module over its inverse image in that degree. -/
public theorem modulePushforward_obj_obj (f : V ⟶ U) (G : Modules V) (W : (ZariskiOpen U)ᵒᵖ) :
    (((modulePushforward f).obj G).val.obj W : Type u) =
      G.val.obj (op ((zariskiPullback f).obj W.unop)) :=
  rfl

/-- The inclusion of the open-set site of one simplicial degree into the total Zariski site is
continuous, by Stacks 09W0. -/
public instance levelFunctor_isContinuous_zariski (X : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) :
    (levelFunctor (zariskiSpace X) n).IsContinuous
      (Opens.grothendieckTopology ((zariskiSpace X).obj n)) (zariskiTopology X) :=
  levelFunctor_isContinuous (zariskiSpace X) n

/-- The structure sheaf of the scheme in degree `n`, read as a morphism of sheaves of rings to
the direct image of `𝒪_X` along the inclusion of the degree-`n` site. It is the inverse of the
identification `structureComponentIso` of the degree-`n` component of `𝒪_X`. -/
public noncomputable def componentStructureHom (X : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) :
    (X.obj n).ringCatSheaf ⟶
      ((levelFunctor (zariskiSpace X) n).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ((zariskiSpace X).obj n)) (zariskiTopology X)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O) where
  hom := Functor.whiskerRight (structureComponentIso X n).inv (forget₂ CommRingCat RingCat.{u})

/-- The degree-`n` component `F_n` of a sheaf of `𝒪_X`-modules on the total Zariski site: its
sections over an open `W` of the scheme `X_n` are the sections of `F` over the object `(n, W)`,
as a module over `Γ(X_n, W)`. -/
public noncomputable def componentModule (X : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) : Modules X ⥤ (X.obj n).Modules :=
  SheafOfModules.pushforward.{u} (F := levelFunctor (zariskiSpace X) n)
    (J := Opens.grothendieckTopology ((zariskiSpace X).obj n)) (K := zariskiTopology X)
    (componentStructureHom X n)

/-- The sections of the degree-`n` component over an open `W` of `X_n` are the sections of the
module over the object `(n, W)` of the total Zariski site. -/
public theorem componentModule_obj_obj (X : SimplicialObject Scheme.{u})
    (n : SimplexCategoryᵒᵖ) (F : Modules X) (W : (Opens ((zariskiSpace X).obj n))ᵒᵖ) :
    (((componentModule X n).obj F).val.obj W : Type u) =
      F.val.obj (op ⟨n, W.unop⟩) :=
  rfl

end AlgebraicGeometry.SimplicialScheme

end
