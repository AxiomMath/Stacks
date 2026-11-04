module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings

/-!
# Compactness of constructible sheaves of modules on the small étale site

Let `X` be a quasi-compact quasi-separated scheme and `Λ` a Noetherian ring. Morphisms out of a
constructible sheaf of `Λ`-modules on `X_étale` commute with filtered colimits: for a filtered
colimit `G = colim G_i` of sheaves of `Λ`-modules, `Mor(F, G) = colim Mor(F, G_i)`. This is the
sheaves-of-modules case of Stacks 09Z4.

Stacks 095N presents such a sheaf as the cokernel of a map between finite direct sums of
extensions by zero of constant free rank-one module sheaves at quasi-compact quasi-separated étale
objects, and `AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation` concludes
compactness from such a presentation given that those objects have cofinal finite coverings with
quasi-compact fibre products. The latter hypothesis is discharged by
`AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`; the presentation is not available in
the library, so Stacks 095N is carried as the named hypothesis `h095N`.

## Main results

* `AlgebraicGeometry.isFinitelyPresentable_of_isConstructibleModuleSheaf` — **the
  sheaves-of-modules case of Stacks 09Z4**, with Stacks 095N as a hypothesis.

## Implementation notes

Compactness is `CategoryTheory.IsFinitelyPresentable`, which says that the covariant Hom functor
preserves filtered colimits; that is exactly the assertion that the canonical map
`colim Mor(F, G_i) → Mor(F, colim G_i)` is a bijection.

The coefficient universes are those forced by part (4) of Stacks 0738 on this site, as explained in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable`: the small
étale site of `B : BigEtaleSite.{u}` is a `Type (u + 1)` with `Category.{u}`, so the ring and the
module both live in `Type (u + 1)`.

`X` is quasi-compact and quasi-separated, not Noetherian; the Noetherian hypothesis is on `Λ`,
where `AlgebraicGeometry.IsConstructibleModuleSheaf` carries it.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The sheaves-of-`Λ`-modules case of Stacks 09Z4.** Let `X` be a quasi-compact quasi-separated
scheme, let `Λ` be a Noetherian ring and let `F` be a constructible sheaf of `Λ`-modules on
`X_étale`. Then morphisms out of `F` commute with filtered colimits of sheaves of `Λ`-modules:
`Mor(F, colim G_i) = colim Mor(F, G_i)`.

Stacks 095N — the presentation of a constructible sheaf of `Λ`-modules as the cokernel of a map
between finite direct sums of extensions by zero of constant free rank-one module sheaves at
quasi-compact quasi-separated étale objects — is carried as the hypothesis `h095N`. It is a
special case of `AlgebraicGeometry.IsConstructibleModuleSheaf.isFinitelyPresentable`, which proves
Stacks 095N. -/
public theorem isFinitelyPresentable_of_isConstructibleModuleSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]
    (h095N : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R),
      IsConstructibleModuleSheaf B X R G →
        HasFiniteShriekPresentation.{u, u + 1, u + 1} B X R
          (fun W ↦ CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) ∧
            QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W)) G)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsFinitelyPresentable.{u + 1} F :=
  isFinitelyPresentable_of_hasFiniteShriekPresentation B X R _
    (fun W hW ↦ SmallEtale.hasFiniteQuasiCompactCoverings B X W hW.1 hW.2) F (h095N F hF)

end AlgebraicGeometry

end
