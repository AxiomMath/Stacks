module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePushforward
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPushforwardQuasicoherentTotal
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentAdjunction

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

* `AlgebraicGeometry.SimplicialScheme.quasicoherentModulePullbackAdjPushforward`:
  **Stacks 07TK**, granted `ModulePushforwardQuasicoherence`. The restricted functors
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

Because the source's three hypotheses on `f` enter its proof of Stacks 07TK only through
Stacks 07TJ, carrying that conclusion makes them redundant. They are stated all the same, so
that the statement is the source's; they are named with a leading underscore to record that the
proof does not use them.

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

/-- **Stacks 07TJ as a functor on quasi-coherent modules.** Pushforward along a cartesian
morphism of simplicial schemes with flat face maps on the target and quasi-compact
quasi-separated components, restricted to the quasi-coherent modules on the two total Zariski
sites. -/
public noncomputable def quasicoherentModulePushforward' (f : V ⟶ U)
    (hcart : NatTrans.Equifibered f)
    (hflat : ∀ (k : ℕ) (j : Fin (k + 2)), Flat (U.δ j))
    (hqc : ∀ k : SimplexCategoryᵒᵖ, QuasiCompact (f.app k))
    (hqs : ∀ k : SimplexCategoryᵒᵖ, QuasiSeparated (f.app k)) :
    QuasicoherentModules V ⥤ QuasicoherentModules U :=
  (isQuasicoherentOnSiteZariski U).lift
    (ObjectProperty.ι (isQuasicoherentOnSiteZariski V) ⋙ modulePushforward f)
    fun G => isQuasicoherentOnSite_modulePushforward f hcart hflat hqc hqs G.obj G.property

/-- **Stacks 07TK.** Let `f : V ⟶ U` be a cartesian morphism of simplicial schemes such that
every face map of `U` is flat and every component `f_n : V_n ⟶ U_n` is quasi-compact and
quasi-separated. Then the pullback `f^*` and the pushforward `f_*` are an adjoint pair between
the category of quasi-coherent modules on `U_Zar` and the category of quasi-coherent modules on
`V_Zar`.

Quasi-coherence of the pullback is Stacks 07TI and of the pushforward is Stacks 07TJ;
adjointness itself is the adjunction of Stacks 03D7 on all sheaves of modules, restricted along
the two full subcategory inclusions. -/
@[stacks 07TK]
public noncomputable def quasicoherentModulePullbackAdjPushforward' (f : V ⟶ U)
    (hcart : NatTrans.Equifibered f)
    (hflat : ∀ (k : ℕ) (j : Fin (k + 2)), Flat (U.δ j))
    (hqc : ∀ k : SimplexCategoryᵒᵖ, QuasiCompact (f.app k))
    (hqs : ∀ k : SimplexCategoryᵒᵖ, QuasiSeparated (f.app k)) :
    quasicoherentModulePullback f ⊣ quasicoherentModulePushforward' f hcart hflat hqc hqs :=
  Adjunction.restrictFullyFaithful (modulePullbackAdjModulePushforward f)
    (isQuasicoherentOnSiteZariski U).fullyFaithfulι
    (isQuasicoherentOnSiteZariski V).fullyFaithfulι
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

end AlgebraicGeometry.SimplicialScheme

end
