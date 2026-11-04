module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves

/-!
# Enough injectives for sheaves of modules on the big sites of schemes

Let `𝒪` be a sheaf of rings on one of the five standard big sites of schemes sliced over a
scheme. The category of `𝒪`-modules with sections in the universe of the schemes is
Grothendieck abelian at that universe, hence has enough injectives. This file records both
facts as instances, so that the right derived functors of a direct image of such modules are
available without any hypothesis beyond the site itself.

## Main results

* `AlgebraicGeometry.BigZariskiOver.isGrothendieckAbelian_sheafOfModules` and
  `AlgebraicGeometry.BigZariskiOver.enoughInjectives_sheafOfModules`, and their four siblings
  for the big étale, smooth, syntomic and fppf slices.

## Implementation notes

The objects of a big slice live one universe above its morphisms, so none of the generic
routes to enough injectives for sheaves of modules applies at the module universe `u`:
Mathlib's `SheafOfModules.instIsGrothendieckAbelian` asks for a site that is small on the
nose, and `SheafOfModules.enoughInjectives_of_univLE` asks for `UnivLE.{u + 1, u}` between
the universe of the objects of the site and the module universe, which is false here.

What does apply is essential smallness, which the slices of the category of schemes below a
cardinal have (`AlgebraicGeometry.essentiallySmall_schemeBelow'`):
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` transports Mathlib's instance along
the equivalence with a small model, asking only for essential smallness at the module universe
together with the two sheafification hypotheses that
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/AbelianSheaves.lean` supplies. That result
is a theorem rather than an instance on purpose: as an instance it would be attempted at every
site in the development. This file applies it once at each of the five big slices, and reads
off the enough injectives of [Stacks, Tag 01DU].

`CategoryTheory.IsGrothendieckAbelian` and `CategoryTheory.EnoughInjectives` are both `Prop`s,
so these instances cannot diamond against any other route to the same goal, and none of them
takes an instance argument of its own class, so none can enter a loop. Each mentions the
topology of one big slice, so none can be tried at any other site.

## References

* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
* [Stacks Project, Tag 020S](https://stacks.math.columbia.edu/tag/020S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigZariskiOver

/-- Sheaves of modules over a sheaf of rings on the big Zariski slice over `S`, with sections
in the universe of the schemes, form a Grothendieck abelian category at that universe. -/
public instance isGrothendieckAbelian_sheafOfModules (B : AlgebraicGeometry.BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

/-- Sheaves of modules over a sheaf of rings on the big Zariski slice over `S`, with sections
in the universe of the schemes, have enough injectives. -/
public instance enoughInjectives_sheafOfModules (B : AlgebraicGeometry.BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end BigZariskiOver

namespace BigEtaleOver

/-- Sheaves of modules over a sheaf of rings on the big étale slice over `S`, with sections in
the universe of the schemes, form a Grothendieck abelian category at that universe. -/
public instance isGrothendieckAbelian_sheafOfModules (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

/-- Sheaves of modules over a sheaf of rings on the big étale slice over `S`, with sections in
the universe of the schemes, have enough injectives. -/
public instance enoughInjectives_sheafOfModules (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end BigEtaleOver

namespace BigSmoothOver

/-- Sheaves of modules over a sheaf of rings on the big smooth slice over `S`, with sections in
the universe of the schemes, form a Grothendieck abelian category at that universe. -/
public instance isGrothendieckAbelian_sheafOfModules (B : AlgebraicGeometry.BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (R : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

/-- Sheaves of modules over a sheaf of rings on the big smooth slice over `S`, with sections in
the universe of the schemes, have enough injectives. -/
public instance enoughInjectives_sheafOfModules (B : AlgebraicGeometry.BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (R : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end BigSmoothOver

namespace BigSyntomicOver

/-- Sheaves of modules over a sheaf of rings on the big syntomic slice over `S`, with sections
in the universe of the schemes, form a Grothendieck abelian category at that universe. -/
public instance isGrothendieckAbelian_sheafOfModules (B : AlgebraicGeometry.BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

/-- Sheaves of modules over a sheaf of rings on the big syntomic slice over `S`, with sections
in the universe of the schemes, have enough injectives. -/
public instance enoughInjectives_sheafOfModules (B : AlgebraicGeometry.BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end BigSyntomicOver

namespace BigFppfOver

/-- Sheaves of modules over a sheaf of rings on the big fppf slice over `S`, with sections in
the universe of the schemes, form a Grothendieck abelian category at that universe. -/
public instance isGrothendieckAbelian_sheafOfModules (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R := R)

/-- Sheaves of modules over a sheaf of rings on the big fppf slice over `S`, with sections in
the universe of the schemes, have enough injectives. -/
public instance enoughInjectives_sheafOfModules (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (R : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end BigFppfOver

end AlgebraicGeometry

end
