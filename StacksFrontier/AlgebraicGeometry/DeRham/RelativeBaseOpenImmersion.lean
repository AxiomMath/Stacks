module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBaseProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# The coefficient spaces along an open immersion

For a morphism of schemes `g : Y ⟶ S` and an open immersion `j : U ⟶ Y`, the morphism of ringed
spaces `(U, (j ∘ g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` along which the de Rham complex of `U` over `S`
is pushed forward to `Y` is an open immersion of ringed spaces: the inverse image of a sheaf along
an open embedding is its restriction, so all its stalk maps are isomorphisms.

## Main results

* `AlgebraicGeometry.RingedSpace.isOpenImmersion_inverseImageCompProjection`: the general
  statement for ringed spaces and open embeddings.
* `Stacks.DeRhamSmooth.isOpenImmersion_relativeBase`: the case of `relativeBase`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **The canonical morphism `(W, (j ∘ i)^{-1}𝒪_S) ⟶ (X, i^{-1}𝒪_S)` is an open immersion when `j`
is an open embedding.** Its composite with the projection of `(X, i^{-1}𝒪_S)` is the projection of
`(W, (j ∘ i)^{-1}𝒪_S)`, and the stalk maps of both projections are isomorphisms. -/
theorem isOpenImmersion_inverseImageCompProjection (S : RingedSpace.{u, u}) {X W : TopCat.{u}}
    (i : X ⟶ S.carrier) (j : W ⟶ X) (hj : IsOpenEmbedding j) :
    SheafedSpace.IsOpenImmersion (inverseImageCompProjection S i j) := by
  have H : ∀ w : W, IsIso ((inverseImageCompProjection S i j).hom.stalkMap w) := fun w => by
    have h1 := isIso_stalkMap_inverseImageProjection S i (j w)
    have h2 := isIso_stalkMap_inverseImageProjection S (j ≫ i) w
    have e := PresheafedSpace.stalkMap.congr_hom
      (inverseImageCompProjection S i j ≫ inverseImageProjection S i).hom
      (inverseImageProjection S (j ≫ i)).hom
      (congrArg (fun φ => φ.hom) (inverseImageCompProjection_comp S i j)) w
    have hcomp : IsIso
        ((inverseImageCompProjection S i j ≫ inverseImageProjection S i).hom.stalkMap w) := by
      rw [e]
      infer_instance
    have hc := PresheafedSpace.stalkMap.comp (inverseImageCompProjection S i j).hom
      (inverseImageProjection S i).hom w
    have hcomp' : IsIso ((inverseImageProjection S i).hom.stalkMap
        ((inverseImageCompProjection S i j).hom.base w) ≫
        (inverseImageCompProjection S i j).hom.stalkMap w) := hc ▸ hcomp
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 hcomp'
  exact SheafedSpace.IsOpenImmersion.of_stalk_iso _ hj (H := H)

end AlgebraicGeometry.RingedSpace

namespace Stacks.DeRhamSmooth

variable {U Y S : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (g : Y ⟶ S)

/-- **The coefficient-space morphism of an open immersion is an open immersion of ringed
spaces.** -/
instance isOpenImmersion_relativeBase : SheafedSpace.IsOpenImmersion (relativeBase j g) :=
  RingedSpace.isOpenImmersion_inverseImageCompProjection S.toRingedSpace g.base j.base
    j.isOpenEmbedding

end Stacks.DeRhamSmooth

end
