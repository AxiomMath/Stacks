module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution

/-!
# The Zariski ringed site of a scheme is the ringed site of its underlying ringed space

`AlgebraicGeometry.Scheme.zariskiRingedSite S` and
`AlgebraicGeometry.RingedSpace.ringedSite S.toRingedSpace` are the same
`AlgebraicGeometry.RingedSite`: the opens of the underlying space, the open-cover topology and
the structure sheaf, in both cases.  This file records that, and the agreement of the two sheaves
of rings the modules live over.

Both are reducible abbreviations and both are literally the same three fields, so the identity is
`rfl`; it was relied on definitionally and never named.  Naming it is what lets a statement about
the derived tensor product of a *ringed space* — `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`
and its comparison with the ringed-site notion,
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_derivedTensorProduct`, both of which are
stated for a datum on `AlgebraicGeometry.RingedSpace.ringedSite X` — be read against a datum on
the small Zariski ringed site of a scheme, which is the shape the comparison with the small étale
site of [Stacks, Tag 08H7] produces.  See the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/TorAmplitudeQuasiCoherentTests.lean`, which records the
absence of this identification as one of the three things the converse of [Stacks, Tag 08IL] is
waiting on.

## Main results

* `AlgebraicGeometry.Scheme.zariskiRingedSite_eq_ringedSite_toRingedSpace`: the two ringed sites
  are equal.
* `AlgebraicGeometry.Scheme.ringSheaf_zariskiRingedSite_eq_structureSheafRing`: so are the two
  sheaves of rings their modules live over.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08IL](https://stacks.math.columbia.edu/tag/08IL)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The small Zariski ringed site of a scheme is the ringed site of its underlying ringed
space.**  Both are the opens of the underlying space with the open-cover topology and the
structure sheaf, so the two `AlgebraicGeometry.RingedSite`s are the same three fields. -/
theorem Scheme.zariskiRingedSite_eq_ringedSite_toRingedSpace (S : Scheme.{u}) :
    S.zariskiRingedSite = RingedSpace.ringedSite S.toRingedSpace :=
  rfl

/-- The sheaf of rings an `𝒪_S`-module lives over, read off the small Zariski ringed site of a
scheme, is the one it lives over read off the underlying ringed space.  This is
`AlgebraicGeometry.RingedSpace.ringSheaf_ringedSite` carried across
`AlgebraicGeometry.Scheme.zariskiRingedSite_eq_ringedSite_toRingedSpace`. -/
theorem Scheme.ringSheaf_zariskiRingedSite_eq_structureSheafRing (S : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) =
      _root_.structureSheafRing S.toRingedSpace :=
  rfl

end AlgebraicGeometry

end
