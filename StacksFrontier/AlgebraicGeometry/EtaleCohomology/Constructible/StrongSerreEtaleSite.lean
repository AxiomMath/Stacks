module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Constructible abelian sheaves on Mathlib's small étale site

The small étale site of Stacks 021B, `AlgebraicGeometry.SmallEtale B X.obj X.property`, is cut
out of a big étale site `B` by a cardinal cutoff, and the library's constructibility predicate
for abelian sheaves, `AlgebraicGeometry.IsConstructibleAbelianSheaf`, is stated there. Mathlib's
small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology` has the same sheaves, the
comparison functor being a dense subsite inclusion
(`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`), and it is the site on which this
library computes étale cohomology. This file carries constructibility, and the strong Serre
property of Stacks 09BH (2), across that identification.

## Main definitions

* `AlgebraicGeometry.IsConstructibleEtaleSiteAbelianSheaf`: constructibility of a sheaf of
  abelian groups on Mathlib's small étale site of `X`, namely constructibility of the sheaf it
  becomes on the small étale site of Stacks 021B.

## Main results

* `AlgebraicGeometry.isConstructibleEtaleSiteAbelianSheaf_of_mono`: a subsheaf of a constructible
  abelian sheaf on Mathlib's small étale site of a Noetherian scheme is constructible.
* `AlgebraicGeometry.isConstructibleEtaleSiteAbelianSheaf_of_epi`: likewise for a quotient sheaf.

## Implementation notes

The identification is `AlgebraicGeometry.SmallEtale.sheafEquiv` at the coefficient category
`AddCommGrpCat.{u + 1}`, whose inverse is the restriction functor
`CategoryTheory.Functor.sheafPushforwardContinuous` along the comparison
`AlgebraicGeometry.SmallEtale.toEtaleSite`. So the predicate below is not a new notion: it says
that the restriction of `F` to the objects of the small étale site of Stacks 021B — which is again
`F`, on a dense subsite — is constructible. The coefficient universe is `AddCommGrpCat.{u + 1}`,
the one at which Stacks 09BH (2) is available in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/StrongSerreAbelian.lean`.

Both transfers are immediate from 09BH (2) on the site of Stacks 021B, because the restriction
functor is an equivalence and so preserves monomorphisms and epimorphisms. For epimorphisms the
instance is produced by hand from the adjunction underlying the equivalence: instance search for
`CategoryTheory.Functor.PreservesEpimorphisms` of the restriction functor exhausts its heartbeat
budget on this site.

**No `@[stacks 09BH]` attribute appears in this file.** The tag for part (2) is carried on the
site of Stacks 021B by
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/StrongSerreAbelian.lean`, and what is
here is the same proposition read through the comparison of sites, not a second proof of it.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
  (X : B.Scheme)

/-- **A constructible sheaf of abelian groups on Mathlib's small étale site of `X`.** The small
étale site of Stacks 021B is a dense subsite of Mathlib's, so the two have the same sheaves, and
`F` is constructible exactly when the sheaf it restricts to on the former is constructible in the
sense of `AlgebraicGeometry.IsConstructibleAbelianSheaf`. -/
public abbrev IsConstructibleEtaleSiteAbelianSheaf
    (F : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  IsConstructibleAbelianSheaf B X
    ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj F)

/-- **Stacks 09BH (2), subsheaves, on Mathlib's small étale site.** A subsheaf of a constructible
sheaf of abelian groups on Mathlib's small étale site of a Noetherian scheme is constructible.

Restriction to the small étale site of Stacks 021B is an equivalence, hence preserves
monomorphisms, and `AlgebraicGeometry.isConstructibleAbelianSheaf_of_mono` applies there. -/
public theorem isConstructibleEtaleSiteAbelianSheaf_of_mono [IsNoetherian X.obj]
    {F G : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}} (i : G ⟶ F) [Mono i]
    (hF : IsConstructibleEtaleSiteAbelianSheaf B X F) :
    IsConstructibleEtaleSiteAbelianSheaf B X G :=
  isConstructibleAbelianSheaf_of_mono B X (smallEtaleUnderlyingSetCommutes B X)
    (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X)
    ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.map i) hF

/-- **Stacks 09BH (2), quotients, on Mathlib's small étale site.** A quotient of a constructible
sheaf of abelian groups on Mathlib's small étale site of a Noetherian scheme is constructible.

Restriction to the small étale site of Stacks 021B is an equivalence, hence preserves
epimorphisms, and `AlgebraicGeometry.isConstructibleAbelianSheaf_of_epi` applies there. -/
public theorem isConstructibleEtaleSiteAbelianSheaf_of_epi [IsNoetherian X.obj]
    {F Q : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}} (p : F ⟶ Q) [Epi p]
    (hF : IsConstructibleEtaleSiteAbelianSheaf B X F) :
    IsConstructibleEtaleSiteAbelianSheaf B X Q :=
  have hpres : (SmallEtale.sheafEquiv B X.obj X.property
      AddCommGrpCat.{u + 1}).inverse.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).symm.toAdjunction
  have : Epi ((SmallEtale.sheafEquiv B X.obj X.property
      AddCommGrpCat.{u + 1}).inverse.map p) := hpres.preserves p
  isConstructibleAbelianSheaf_of_epi B X (smallEtaleUnderlyingSetCommutes B X)
    (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X)
    ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.map p) hF

end AlgebraicGeometry

end
