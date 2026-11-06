module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QcqsVanishingFromAffineOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Transport of the vanishing of the cohomology of an arbitrary abelian sheaf between sites

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` and carry a terminal object of
`C` to a terminal object of `D`. Restriction of abelian sheaves along `G` is then an equivalence
of sheaf categories, and it carries the constant sheaf on a group to the constant sheaf on that
group. Since `CategoryTheory.Sheaf.H` is `Ext` out of the constant sheaf on `ULift ℤ`, an abelian
sheaf on `(D, K)` and its restriction to `(C, J)` therefore have the same cohomology in every
degree — and in particular one of those groups vanishes exactly when the other does.

This removes the restriction to *constant* sheaves from
`Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite` and its
primed variant, with the same hypotheses and the same latitude in the universes: the two sites
live in unrelated universes, and the `Ext`-universe of each of the two sheaf categories is
independent of the other's. That latitude is what
`CategoryTheory.sheafCohomologyIsoOfIsEquivalence` does not offer — it forces the two
`Ext`-universes to agree — and it is what makes these statements usable when one of the two
sheaf categories has `Ext`-groups only in its own morphism universe while the other is handed an
arbitrary one.

## Main results

* `DenseSubsiteSheaf.subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite`:
  for an arbitrary abelian sheaf on the larger site, the transport of the vanishing of its
  cohomology from the dense subsite to that site. The other direction is
  `Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite`.
* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_smallEtale_of_affineOpens_acyclic`:
  **global étale cohomology vanishing on Mathlib's small étale site from acyclicity on the
  affine opens.** The conclusion of
  `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affineOpens_acyclic`, which is proved
  on the one-universe model of the small étale site, carried onto
  `AlgebraicGeometry.Scheme.smallEtaleTopology`.

## Implementation notes

The equivalence of sheaf categories is
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, whose inverse functor is restriction along
`G` on the nose, and the identification of the two constant sheaves is Mathlib's
`CategoryTheory.equivCommuteConstant` together with its primed variant. Vanishing is transported
by `Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence`, which crosses the two
`Ext`-universes, and the object out of which `Ext` is taken is moved to its intended spelling by
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source`.

The dense subsite inclusion used in the geometric application is `CategoryTheory.AsSmall.down`
out of the one-universe model of the small étale site, which is a dense subsite inclusion
because that model carries the induced topology; the terminal object it has to preserve is `X`
itself, read as an object of its own small étale site, and `AsSmall.down` preserves it because
it is an equivalence.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.AbsolutelyIntegrallyClosed (SectionsSub)
open Stacks.EtaleCohomology.StrictlyHenselian (opensCohomology)

universe w w' v₁ u₁ v₂ u₂ a u

namespace Stacks.Cohomology.DenseSubsiteSheaf

/-- **The cohomology of an abelian sheaf does not change on a dense subsite**, read from the
subsite to the larger site: for an abelian sheaf `F` on `(D, K)`, the vanishing of the
degree-`q` cohomology of the restriction of `F` to the dense subsite `(C, J)` gives the vanishing
of the degree-`q` cohomology of `F` itself.

No hypothesis on `F` is made; the `Ext` universes on the two sides are unrelated. -/
public theorem subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w}
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F) q)) :
    Subsingleton (Sheaf.H.{w'} F q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : E.symm.functor.Additive := ⟨by intro X Y f g; ext U; exact rfl⟩
  have : E.functor.Additive := Equivalence.inverse_additive E.symm
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))) q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) F q h)

end Stacks.Cohomology.DenseSubsiteSheaf

namespace Stacks.EtaleCohomology.MayerVietoris

open Stacks.Cohomology.DenseSubsiteSheaf

/-- An abelian sheaf on Mathlib's small étale site of `X`, read on the one-universe model
`Stacks.EtaleCohomology.MayerVietoris.Site X` of that site: restriction along `AsSmall.down`,
which is where `CategoryTheory.Sheaf.H'` and the Mayer--Vietoris sequence of [Stacks, Tag 0A50]
are available. -/
public abbrev mayerVietorisRestrict (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  (AsSmall.down : Site X ⥤ X.Etale).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology X) X.smallEtaleTopology

/-- `X` itself, read as an object of `X.Etale` through the identity of `X`, is a terminal object
there: it is the image under the equivalence `AsSmall.down` of the terminal object
`Stacks.EtaleCohomology.MayerVietoris.self X` of the one-universe model. -/
public def isTerminalAsSmallDownSelf (X : Scheme.{u}) :
    IsTerminal ((AsSmall.down : Site X ⥤ X.Etale).obj (self X)) :=
  (selfIsTerminal X).isTerminalObj (AsSmall.down : Site X ⥤ X.Etale) _

/-- **Global étale cohomology vanishing from acyclicity on the affine opens, on Mathlib's small
étale site.** Let `X` be a quasi-compact quasi-separated scheme and let `F` be an abelian sheaf
on `AlgebraicGeometry.Scheme.smallEtaleTopology`, Mathlib's small étale site of `X`. If the
restriction of `F` to the one-universe model of that site is acyclic in positive degrees over
every affine open of `X`, and if for every quasi-compact open `U` and affine open `V` each
degree-zero section of that restriction over `U ⊓ V` is a difference of sections over `U` and
over `V`, then `H^q(X, F) = 0` for every `q > 0`.

This is `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_affineOpens_acyclic`, which is
proved on the one-universe model, carried across the dense subsite inclusion `AsSmall.down` by
`DenseSubsiteSheaf.subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite`.
The `Ext`-universe of
the conclusion is arbitrary: the model's own `Ext`-groups, in which the hypothesis is read, are
in the successor of the scheme universe. -/
public theorem subsingleton_H_smallEtale_of_affineOpens_acyclic {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (haff : ∀ V : X.Opens, IsAffineOpen V → ∀ n, 0 < n →
      Subsingleton ((opensCohomology ((mayerVietorisRestrict X).obj F) n).obj (op V)))
    (hsub : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V →
      SectionsSub ((mayerVietorisRestrict X).obj F) U V)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} F q) :=
  subsingleton_H_of_subsingleton_H_restriction_of_isDenseSubsite (topology X) X.smallEtaleTopology
    (AsSmall.down : Site X ⥤ X.Etale) (selfIsTerminal X) (isTerminalAsSmallDownSelf X) F q
    (subsingleton_H_of_affineOpens_acyclic ((mayerVietorisRestrict X).obj F) haff hsub q hq)

end Stacks.EtaleCohomology.MayerVietoris

end
