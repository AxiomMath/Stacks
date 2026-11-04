module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentSpellings
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TopCohomologyFinitenessGeneral

/-!
# Stacks 08FX, finite type of the top cohomology, at the two ringed sites of Stacks 08HE

Stacks 08HE compares pseudo-coherence on the small Zariski ringed site of a scheme with
pseudo-coherence on its small étale ringed site. The two sites sit at different universes: the
Zariski one is an `AlgebraicGeometry.RingedSite.{u, u, u}` and the étale one an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, both with sections in `Type u`. This module
specializes `AlgebraicGeometry.RingedSite.isFiniteType_homology_general` to each of them, which
is the form in which the argument for clause (2) ⇒ (1) of Stacks 08HE uses Stacks 08FX.

Neither specialization is reachable from
`AlgebraicGeometry.RingedSite.isFiniteType_homology`, which is stated at
`RingedSite.{u, u, 0}` and `SheafOfModules.{0}`: the module sections there are in `Type 0`,
while on both of these sites they are in `Type u`, and the étale site moreover has its objects
one universe above its morphisms.

## Main results

* `AlgebraicGeometry.Scheme.isFiniteType_homology_zariskiRingedSite`
* `AlgebraicGeometry.SmallEtale.isFiniteType_homology_smallEtaleRingedSite`

## Implementation notes

Each statement is one application of the universe-general theorem. The typeclass hypotheses it
carries — left exact sheafification of abelian presheaves and local bijectivity of the weak
equivalences, on the site and on each of its slices, plus composition with
`RingCat ⥤ AddCommGrpCat` on each slice — are found by instance search at both sites, which is
what
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentSpellings.lean`
records; both ringed sites are reducible abbreviations, so the instances stated for
`AlgebraicGeometry.Opens.grothendieckTopology` and `AlgebraicGeometry.SmallEtale.topology` are
found at their `.J` projections. The derived-category model is taken as a hypothesis, at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling in which the pseudo-coherence predicate asks
for one; for the étale site that spelling is supplied from the
`AlgebraicGeometry.SmallEtale.structureSheaf` one by
`AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite`.

No `@[stacks 08HE]` attribute is claimed: nothing here is a clause of that tag. The
`@[stacks 08FX]` attribute sits on the universe-general theorem these specialize.

## References

* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry

/-- **Stacks 08FX, finite type of the top cohomology, on the small Zariski ringed site of a
scheme.** An `m`-pseudo-coherent object of `D(𝒪_X)` whose cohomology vanishes above `m` has
`H^m` of finite type.

The site is an `AlgebraicGeometry.RingedSite.{u, u, u}` and the modules are
`SheafOfModules.{u}`, so this is a specialization of
`AlgebraicGeometry.RingedSite.isFiniteType_homology_general` and not of
`AlgebraicGeometry.RingedSite.isFiniteType_homology`. -/
public theorem Scheme.isFiniteType_homology_zariskiRingedSite (X : Scheme.{u})
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
    (m : ℤ)
    (hK : X.zariskiRingedSite.IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))
          i).obj K)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))
        m).obj K).IsFiniteType :=
  RingedSite.isFiniteType_homology_general X.zariskiRingedSite K m hK hvanish

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **Stacks 08FX, finite type of the top cohomology, on the small étale ringed site of a
scheme.** An `m`-pseudo-coherent object of `D(𝒪_étale)` whose cohomology vanishes above `m` has
`H^m` of finite type.

The site is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}` — its objects lie one universe above
its morphisms and its sections — and the modules are `SheafOfModules.{u}`, so this is a
specialization of `AlgebraicGeometry.RingedSite.isFiniteType_homology_general` and not of
`AlgebraicGeometry.RingedSite.isFiniteType_homology`. -/
public theorem isFiniteType_homology_smallEtaleRingedSite
    [HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O))]
    (K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O)))
    (m : ℤ)
    (hK : (smallEtaleRingedSite B X hX).IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O)) i).obj K)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B X hX).O)) m).obj
          K).IsFiniteType :=
  RingedSite.isFiniteType_homology_general (smallEtaleRingedSite B X hX) K m hK hvanish

end SmallEtale

end AlgebraicGeometry

end
