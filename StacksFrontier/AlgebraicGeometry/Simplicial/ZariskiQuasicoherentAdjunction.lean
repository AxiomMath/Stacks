module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePushforward
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback and pushforward as an adjoint pair on quasi-coherent modules

Let `f : V ⟶ U` be a morphism of simplicial schemes. Pullback and pushforward of sheaves of
modules on the total Zariski sites are an adjoint pair `f^* ⊣ f_*` between all sheaves of
modules, by Stacks 03D7. Stacks 07TK asserts that the pair restricts to the quasi-coherent
modules: for `f` cartesian, with flat face maps on `U` and quasi-compact quasi-separated
components, both functors carry quasi-coherent modules to quasi-coherent modules, and the
restricted functors are again adjoint.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.QuasicoherentModules`: the category of quasi-coherent
  modules on the total Zariski site of a simplicial scheme, the full subcategory of
  `AlgebraicGeometry.SimplicialScheme.Modules` cut out by Stacks 03DL (6).
* `AlgebraicGeometry.SimplicialScheme.ModulePushforwardQuasicoherence`: the statement that `f_*`
  carries quasi-coherent modules on `V_Zar` to quasi-coherent modules on `U_Zar`.
* `AlgebraicGeometry.SimplicialScheme.quasicoherentModulePullback` and
  `.quasicoherentModulePushforward`: the two functors between the quasi-coherent full
  subcategories.

## Main results

* `AlgebraicGeometry.SimplicialScheme.quasicoherentModulePullbackAdjPushforward'`, in
  `StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentAdjunctionUnconditional`:
  **Stacks 07TK**, built on the definitions here. The restricted functors
  `f^* : QCoh(U_Zar) ⥤ QCoh(V_Zar)` and `f_* : QCoh(V_Zar) ⥤ QCoh(U_Zar)` are an adjoint pair.

## Implementation notes

The source's proof has two halves. That the two functors land in the quasi-coherent modules is
Stacks 07TI for the pullback and Stacks 07TJ for the pushforward; granted that, adjointness is
immediate, being the restriction of the adjunction on all modules along two fully faithful full
subcategory inclusions. That restriction is
`CategoryTheory.Adjunction.restrictFullyFaithful`, and the two comparison isomorphisms it asks
for are identities: each restricted functor is by construction the lift of the composite of the
inclusion with the unrestricted functor, so composing it back with the inclusion returns that
composite on the nose.

Of the first half only the pullback is available. Stacks 07TI is
`AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_modulePullback`, and it is used here
rather than assumed. For the pushforward the development proves only that the *components*
`(f_*G)_n` are quasi-coherent
(`AlgebraicGeometry.SimplicialScheme.isQuasicoherent_componentModule_modulePushforward`, which
is where quasi-compactness and quasi-separatedness of the components of `f` enter) and that
`f_*G` is cartesian when `G` is
(`AlgebraicGeometry.SimplicialScheme.isCartesianModule_modulePushforward`, which is where
flatness of the face maps of `U` and cartesianness of `f` enter). Passing from those two facts
to quasi-coherence of `f_*G` on the total Zariski site is the right-to-left direction of
Stacks 0D7M, of which
`CategoryTheory.SimplicialSiteSituation.IsCartesianWithQuasicoherentComponents` carries only the
right-hand side; neither direction of the equivalence is proved. The conclusion of Stacks 07TJ
is therefore carried as the hypothesis `ModulePushforwardQuasicoherence`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
* [Stacks Project, Tag 07TJ](https://stacks.math.columbia.edu/tag/07TJ)
* [Stacks Project, Tag 07TK](https://stacks.math.columbia.edu/tag/07TK)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- The object property cutting out the quasi-coherent sheaves of modules on the total Zariski
site of a simplicial scheme, in the sense of Stacks 03DL (6). -/
public abbrev isQuasicoherentOnSiteZariski (X : SimplicialObject Scheme.{u}) :
    ObjectProperty (Modules X) :=
  SheafOfModules.isQuasicoherentOnSite _

/-- The category `QCoh(X_Zar)` of quasi-coherent sheaves of modules on the total Zariski site of
a simplicial scheme. -/
public abbrev QuasicoherentModules (X : SimplicialObject Scheme.{u}) :=
  (isQuasicoherentOnSiteZariski X).FullSubcategory

/-- **The conclusion of Stacks 07TJ.** The direct image along a morphism of simplicial schemes
carries quasi-coherent sheaves of modules on the total Zariski site of the source to
quasi-coherent sheaves of modules on the total Zariski site of the target. -/
public def ModulePushforwardQuasicoherence (f : V ⟶ U) : Prop :=
  ∀ G : Modules V, G.IsQuasicoherentOnSite →
    ((modulePushforward f).obj G).IsQuasicoherentOnSite

/-- **Stacks 07TI as a functor on quasi-coherent modules.** Pullback along a morphism of
simplicial schemes, restricted to the quasi-coherent modules on the two total Zariski sites. -/
public noncomputable def quasicoherentModulePullback (f : V ⟶ U) :
    QuasicoherentModules U ⥤ QuasicoherentModules V :=
  (isQuasicoherentOnSiteZariski V).lift
    (ObjectProperty.ι (isQuasicoherentOnSiteZariski U) ⋙ modulePullback f)
    fun F => isQuasicoherentOnSite_modulePullback f F.property

/-- Pushforward along a morphism of simplicial schemes, restricted to the quasi-coherent modules
on the two total Zariski sites, granted the conclusion of Stacks 07TJ. -/
public noncomputable def quasicoherentModulePushforward (f : V ⟶ U)
    (hf : ModulePushforwardQuasicoherence f) :
    QuasicoherentModules V ⥤ QuasicoherentModules U :=
  (isQuasicoherentOnSiteZariski U).lift
    (ObjectProperty.ι (isQuasicoherentOnSiteZariski V) ⋙ modulePushforward f)
    fun G => hf G.obj G.property

end AlgebraicGeometry.SimplicialScheme

end
