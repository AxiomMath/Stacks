module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Local Noetherianity is local in the fppf topology

A scheme is locally Noetherian if and only if the members of an fppf covering family are.
Since an étale covering family is an fppf covering family, the same holds for étale
coverings.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_isLocal_fppf` gives fppf locality of local
  Noetherianity.
* `AlgebraicGeometry.isLocallyNoetherian_isLocal_etale` gives its étale locality.
* `AlgebraicGeometry.isNoetherianRing_Γ_of_isLocallyNoetherian`: an affine locally Noetherian
  scheme has Noetherian ring of global sections.

## Implementation notes

Ascent is local Noetherianity of a scheme of finite type over a locally Noetherian base;
descent is the ring-theoretic descent of the Noetherian property along a faithfully flat
ring map, applied to the global sections of the affine schemes involved.

Étale locality is read off the fppf statement through
`AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage` and
`CategoryTheory.ObjectProperty.IsLocal.of_le`; locality for a coarser precoverage is the
stronger statement, so nothing beyond that inclusion is needed.

## References

* [Stacks Project, Tag 034C](https://stacks.math.columbia.edu/tag/034C)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **An affine locally Noetherian scheme has Noetherian ring of global sections.**  The whole
scheme is one of its own affine opens, and local Noetherianity is Noetherianity of the ring of
each of them. -/
theorem isNoetherianRing_Γ_of_isLocallyNoetherian (X : Scheme.{u}) (hX : IsAffine X)
    (hXN : IsLocallyNoetherian X) : IsNoetherianRing (Scheme.Γ.obj (Opposite.op X)) :=
  have := hX
  have := hXN
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩

private instance isLocallyNoetherian_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => IsLocallyNoetherian X) :=
  ⟨fun e _ => isLocallyNoetherian_of_isOpenImmersion e.inv⟩

private instance isLocallyNoetherian_isLocal_zariski :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      Scheme.zariskiPrecoverage :=
  ObjectProperty.IsLocal.mk_of_zeroHypercover fun _ 𝒰 => isLocallyNoetherian_iff_openCover 𝒰

/-- **Stacks Project, Tag 034C.** Being locally Noetherian is local for fppf coverings of
schemes. -/
@[stacks 034C]
instance isLocallyNoetherian_isLocal_fppf :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      Scheme.fppfPrecoverage := by
  refine isLocal_fppfPrecoverage_of_affine
    (fun X : Scheme.{u} => IsLocallyNoetherian X) ?_ ?_
  · intro X S _ _ f _ hfp hSNoeth
    let : IsLocallyNoetherian S := hSNoeth
    let : LocallyOfFinitePresentation f := hfp.1
    exact LocallyOfFiniteType.isLocallyNoetherian f
  · intro X S hX hS f hflat _ hsurj hXNoeth
    let : IsAffine X := hX
    let : IsAffine S := hS
    exact isLocallyNoetherian_of_affine_cover
      (S := fun _ : Unit => ⟨⊤, isAffineOpen_top S⟩) (by simp) fun _ =>
        descent_noetherian (f.appTop).hom
          ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨hflat, hsurj⟩)
          (isNoetherianRing_Γ_of_isLocallyNoetherian X hX hXNoeth)

/-- Being locally Noetherian is local for étale coverings of schemes: a scheme is locally
Noetherian if and only if the members of an étale covering family are. -/
instance isLocallyNoetherian_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

end AlgebraicGeometry
