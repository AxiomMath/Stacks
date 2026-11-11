module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian

/-!
# Tensor products of quasi-coherent modules on the small étale site

Stacks 0GNB asserts six closure properties of the quasi-coherent modules on the small étale site
of a scheme.  **This file is the fifth of them**: the tensor product of two quasi-coherent
`𝒪`-modules on `S_étale` is quasi-coherent.

Unlike the other five, this clause needs neither Stacks 03DW nor Stacks 03DX.  Quasi-coherence of
a sheaf of modules on a site, `SheafOfModules.IsQuasicoherentOnSite`, is the local condition of
Stacks 03DL (6), and the obstruction to closure under an operation is that the two arguments are
presented on two unrelated coverings.  For a *binary* operation that obstruction is removable:
the objects admitting an arrow into a member of each of the two covering families again cover,
and over such an object both presentations restrict.  So the clause follows from the statement
for an arbitrary ringed site,
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite` (Stacks 03L6),
with no input special to the étale topology.

## Main results

* `AlgebraicGeometry.SmallEtale.tensorSheaf_isQuasicoherentOnSite` — **the tensor product clause
  of Stacks 0GNB** on the small étale site of a scheme, with no hypothesis.

## Implementation notes

Sheaves of modules on the small étale site are indexed by the `RingCat`-valued
`AlgebraicGeometry.SmallEtale.structureSheaf` of Stacks 03DU, while the tensor product of
sheaves of modules is formed over a `CommRingCat`-valued structure sheaf, as it must be.  The two
are joined by `AlgebraicGeometry.SmallEtale.sheafCompose_forget₂_commRingStructureSheaf`, which
is an equality by `rfl`, so the statement below is phrased at the `RingCat` spelling its
consumers use and the general theorem applies to it directly.

The sheafification data the general theorem consumes is supplied by
`AlgebraicGeometry.SmallEtale.hasSheafify` and
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective`, which hold because the small étale site
is essentially small.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf of rings underlying the structure sheaf of commutative rings of the small étale
site is the structure sheaf of rings of Stacks 03DU, in the `CategoryTheory.Sheaf.toRingCat`
spelling in which the tensor product of sheaves of modules names its coefficients. -/
public theorem toRingCat_commRingStructureSheaf :
    Sheaf.toRingCat.{u, u + 1, u} (topology B S hS) (commRingStructureSheaf B S hS) =
      structureSheaf B S hS :=
  rfl

/-- **The tensor product clause of Stacks 0GNB.**  The tensor product of two quasi-coherent
`𝒪`-modules on the small étale site of a scheme is quasi-coherent. -/
@[stacks 0GNB "clause (5): the tensor product of two quasi-coherent modules is quasi-coherent"]
public theorem tensorSheaf_isQuasicoherentOnSite
    (F G : SheafOfModules.{u} (structureSheaf B S hS))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    SheafOfModules.IsQuasicoherentOnSite
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (commRingStructureSheaf B S hS))).obj (F, G)) := by
  let hF : SheafOfModules.IsQuasicoherentOnSite
      (R := Sheaf.toRingCat.{u, u + 1, u} (topology B S hS) (commRingStructureSheaf B S hS))
      F := ‹F.IsQuasicoherentOnSite›
  let hG : SheafOfModules.IsQuasicoherentOnSite
      (R := Sheaf.toRingCat.{u, u + 1, u} (topology B S hS) (commRingStructureSheaf B S hS))
      G := ‹G.IsQuasicoherentOnSite›
  exact Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite
    (topology B S hS) (commRingStructureSheaf B S hS) F G

end AlgebraicGeometry.SmallEtale

end
