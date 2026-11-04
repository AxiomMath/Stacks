module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianModuleFaces
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiPushforwardCartesian

/-!
# The direct image of a cartesian module along a cartesian morphism is cartesian

Let `f : V ⟶ U` be a cartesian morphism of simplicial schemes whose base has flat face
morphisms and whose components are quasi-compact and quasi-separated, and let `G` be a sheaf of
`𝒪_V`-modules on the total Zariski site of `V` which is cartesian with quasi-coherent
components. Then the direct image `f_*G` is cartesian on the total Zariski site of `U`.

`AlgebraicGeometry.SimplicialScheme.isIso_componentModuleTransition_modulePushforward` gives
this at a single map of simplicial degrees whose image under `U` is flat; the source's
hypothesis of flatness holds for the face maps only, and Stacks 07TG (3) — available here as
`AlgebraicGeometry.SimplicialScheme.isCartesianModule_iff_faces` — is what turns the faces into
all of `Δ`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isCartesianModule_modulePushforward`: the direct image of
  a cartesian module with quasi-coherent components along a cartesian morphism of simplicial
  schemes is cartesian, under the hypotheses of Stacks 07TJ.

## Implementation notes

The face map `d^{k+1}_i : U_{k+1} ⟶ U_k` is `SimplicialObject.δ`, which is by definition
`U.map (SimplexCategory.δ i).op`, so the flatness hypothesis is passed to the single-degree
statement as a local instance without any transport. The quasi-compactness and
quasi-separatedness of the components and the quasi-coherence of the components of `G` are
likewise instance arguments there, and the degree at which they are needed is the target
`op ⦋k⦌` of the face map.

**What this is, and what it is not.** This is the cartesian half of the source's proof of
Stacks 07TJ. The other half — that `f_*G` is quasi-coherent on the total Zariski site of `U` —
needs the converse direction of Stacks 0D7M, which this development does not have; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ZariskiPushforwardCartesian.lean` and of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/QuasicoherentCartesian.lean`.
The statement is therefore left untagged: it is an intermediate step of 07TJ and not a result
the source delimits.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 07TJ](https://stacks.math.columbia.edu/tag/07TJ)
* [Stacks Project, Tag 0249](https://stacks.math.columbia.edu/tag/0249)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

/-- **The direct image of a cartesian module is cartesian.** Let `f : V ⟶ U` be a cartesian
morphism of simplicial schemes such that the face maps of `U` are flat and every component
`f_k` is quasi-compact and quasi-separated. If `G` is a cartesian sheaf of `𝒪_V`-modules on the
total Zariski site of `V` with quasi-coherent components, then `f_*G` is cartesian on the total
Zariski site of `U`.

These are the hypotheses of Stacks 07TJ, with quasi-coherence of `G` on the total site replaced
by the right-hand side of Stacks 0D7M, which is what the source's proof uses. -/
public theorem isCartesianModule_modulePushforward {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) (hf : NatTrans.Equifibered f)
    (hflat : ∀ (k : ℕ) (j : Fin (k + 2)), Flat (U.δ j))
    (hqc : ∀ k : SimplexCategoryᵒᵖ, QuasiCompact (f.app k))
    (hqs : ∀ k : SimplexCategoryᵒᵖ, QuasiSeparated (f.app k))
    (G : Modules V) (hG : IsCartesianModule V G)
    (hqcoh : ∀ k : SimplexCategoryᵒᵖ, ((componentModule V k).obj G).IsQuasicoherent) :
    IsCartesianModule U ((modulePushforward f).obj G) := by
  rw [isCartesianModule_iff_faces]
  intro k i
  have hFlat : Flat (U.map (SimplexCategory.δ i).op) := hflat k i
  have := hqc (op (SimplexCategory.mk k))
  have := hqs (op (SimplexCategory.mk k))
  have := hqcoh (op (SimplexCategory.mk k))
  exact isIso_componentModuleTransition_modulePushforward f hf _ G (hG _)

end AlgebraicGeometry.SimplicialScheme

end
