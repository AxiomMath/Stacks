module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Sheafification of abelian sheaves on the big sites of schemes

The underlying category of each of the five standard big sites of schemes is the category of
schemes below a cardinal, which is essentially small; so are its slices over an object. Therefore
abelian presheaves on any of those categories can be sheafified with coefficients in the *same*
universe as the morphisms of the site, and the weak equivalences of the topology are exactly the
locally bijective morphisms. Both facts are recorded here as instances.

## Main results

* `AlgebraicGeometry.essentiallySmall_schemeBelow'`: the category of schemes below a cardinal is
  essentially small — the instance form of `AlgebraicGeometry.essentiallySmall_schemeBelow`.
* `AlgebraicGeometry.BigZariskiOver.hasSheafify'`, `AlgebraicGeometry.BigEtaleOver.hasSheafify'`,
  `AlgebraicGeometry.BigSmoothOver.hasSheafify'`, `AlgebraicGeometry.BigSyntomicOver.hasSheafify'`
  and `AlgebraicGeometry.BigFppfOver.hasSheafify'`: abelian presheaves on the big slice sites can
  be sheafified.
* `AlgebraicGeometry.BigZariskiOver.wEqualsLocallyBijective'` and the corresponding instances for
  the étale, smooth, syntomic and fppf slices: the weak equivalences are the locally bijective
  morphisms of abelian presheaves.

## Implementation notes

Mathlib's `CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` are lemmas rather
than instances, since as instances they would be tried on every site. They are instantiated here
at the five big-site topologies, where essential smallness is available and the coefficients are
abelian groups in the universe of the site's morphisms.

The objects of a big site live one universe above its morphisms, so the generic sheafification
instances — which need the coefficient category to have limits indexed by the objects — do not
apply to coefficients in the lower universe; essential smallness is what replaces them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The category of schemes below a cardinal is essentially small.** This is the instance form
of `AlgebraicGeometry.essentiallySmall_schemeBelow`. -/
public instance essentiallySmall_schemeBelow' (κ : Cardinal.{u}) :
    EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow κ) :=
  AlgebraicGeometry.essentiallySmall_schemeBelow κ

namespace BigZariskiOver

/-- Abelian presheaves on the big Zariski slice over `S` can be sheafified. -/
public instance hasSheafify' (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    HasSheafify (AlgebraicGeometry.BigZariskiOver.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- The weak equivalences of the big Zariski slice over `S` are the locally bijective
morphisms of abelian presheaves. -/
public instance wEqualsLocallyBijective' (B : AlgebraicGeometry.BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigZariskiOver.topology B S hS).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

end BigZariskiOver

namespace BigEtaleOver

/-- Abelian presheaves on the big étale slice over `S` can be sheafified. -/
public instance hasSheafify' (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    HasSheafify (AlgebraicGeometry.BigEtaleOver.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- The weak equivalences of the big étale slice over `S` are the locally bijective morphisms
of abelian presheaves. -/
public instance wEqualsLocallyBijective' (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigEtaleOver.topology B S hS).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

end BigEtaleOver

namespace BigSmoothOver

/-- Abelian presheaves on the big smooth slice over `S` can be sheafified. -/
public instance hasSheafify' (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    HasSheafify (AlgebraicGeometry.BigSmoothOver.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- The weak equivalences of the big smooth slice over `S` are the locally bijective morphisms
of abelian presheaves. -/
public instance wEqualsLocallyBijective' (B : AlgebraicGeometry.BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    (AlgebraicGeometry.BigSmoothOver.topology B S hS).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

end BigSmoothOver

namespace BigSyntomicOver

/-- Abelian presheaves on the big syntomic slice over `S` can be sheafified. -/
public instance hasSheafify' (B : AlgebraicGeometry.BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    HasSheafify (AlgebraicGeometry.BigSyntomicOver.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- The weak equivalences of the big syntomic slice over `S` are the locally bijective
morphisms of abelian presheaves. -/
public instance wEqualsLocallyBijective' (B : AlgebraicGeometry.BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigSyntomicOver.topology B S hS).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

end BigSyntomicOver

namespace BigFppfOver

/-- Abelian presheaves on the big fppf slice over `S` can be sheafified. -/
public instance hasSheafify' (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- The weak equivalences of the big fppf slice over `S` are the locally bijective morphisms
of abelian presheaves. -/
public instance wEqualsLocallyBijective' (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigFppfOver.topology B S hS).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

end BigFppfOver

end AlgebraicGeometry

end
