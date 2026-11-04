module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Degree-zero cohomology of the associated module on a big site of schemes

Let `S` be a scheme, let `𝓕` be a quasi-coherent `𝒪_S`-module, and let `τ` be one of the five
topologies `Zariski, étale, smooth, syntomic, fppf`.  The associated module `𝓕^a` on the big
site `(Sch/S)_τ` has, over each open `U ⊆ S` viewed as an object of that site, the same group of
sections as `𝓕` has over `U`:

```
Γ(U, 𝓕)  =  Γ(U, 𝓕^a).
```

This is the unit of the associated-module adjunction being an isomorphism, which holds at every
quasi-coherent module because the pullback-sections presheaf of such a module is already a sheaf
for each of the five topologies.  Degree-zero sheaf cohomology over an object of a site is the
group of sections over that object, so the displayed equality of sections is an equality of
degree-zero cohomology groups,

```
H^0(U, 𝓕)  =  H^0(U, 𝓕^a),
```

and at `U = ⊤`, which is a terminal object of both sites, it is the comparison of the
cohomology of the scheme with the cohomology of the big site:

```
H^0(S, 𝓕)  =  H^0((Sch/S)_τ, 𝓕^a).
```

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAbelianSheafIso`: the isomorphism of
  abelian sheaves on the small Zariski site of `S` between `𝓕` and the restriction of `𝓕^a`
  along the inclusion of the small Zariski site into `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSectionsIso`: its value over an open `U`,
  the identification `Γ(U, 𝓕) ≅ Γ(U, 𝓕^a)`.

## Main results

* `AlgebraicGeometry.BigFppfOver.h'ZeroBaseAssociatedModuleAddEquiv`: the degree-zero cohomology
  of `𝓕` over an open `U` of `S` agrees with the degree-zero cohomology of `𝓕^a` over `U` as an
  object of `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`: **the case `q = 0` of
  clause (1) of [Stacks, Tag 03DW]** — the degree-zero cohomology of the scheme `S` with values
  in `𝓕` agrees with the degree-zero cohomology of the site `(Sch/S)_τ` with values in `𝓕^a`,
  for each of the five topologies.

## Implementation notes

Cohomology of a site is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-group out of the constant
abelian sheaf `ULift ℤ`, and cohomology over an object is `CategoryTheory.Sheaf.H'`; the two
agree over a terminal object, which is how the statement about the site is obtained from the
statement about sections.  On the small Zariski site of `S` the terminal object is the open `⊤`
and on `(Sch/S)_τ` it is that same open viewed as an object of the big site, so a single
identification of sections serves both sides.

Both comparisons are of *abelian* sheaves: the sections of `𝓕` over `U` and the sections of
`𝓕^a` over `U` are modules over different rings — `Γ(U, 𝒪_S)` and the global functions of the
open subscheme `U` — which the structure-sheaf half of the morphism of ringed sites identifies,
but the comparison of cohomology is a statement about the underlying abelian sheaves and does
not need that identification.  Passing to abelian sheaves also makes the restriction of `𝓕^a`
have *literally* the sections of `𝓕^a` over the image open, so no transport appears.

The `CategoryTheory.HasExt` arguments are the ones Mathlib's cohomology of a site takes: without
them `Sheaf.H` is not defined.  On the small Zariski site of `S` they are found by instance
search; on a big site of schemes they are not, the site having its objects one universe above
its morphisms, and they are taken as instance arguments here exactly as in
`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyComparison`.  The `HasSheafify`
arguments are discharged, on both sides, from essential smallness of the site.

Only `q = 0` is treated *here*, and that is a statement about this file and not about the
development.  The positive-degree half of [Stacks, Tag 03DW] is proved elsewhere, and carries
the tag:

* clause (1), every degree and all five `τ` at once, is
  `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso`;
* clause (2) in its small étale half, every degree, is
  `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`;
* clause (2) in its small Zariski half, every degree, is
  `AlgebraicGeometry.smallZariskiQuasiCoherentGlobalCohomologyIso`.

The first two also carry `@[stacks 03P2]`: Descent Proposition 35.9.3 and Étale Cohomology
Theorem 59.22.4 are the same assertion in two chapters.  The vanishing of `H^p(U, 𝓕^a)` for
affine `U` that the source's proof passes through is
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` on a big site and
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine` on the small étale site, both
hypothesis-free.  Their Čech input is
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`, which is
[Stacks, Tag 03FJ] with the degreewise identification
`Γ(V ×_U ⋯ ×_U V, 𝓕^a) = A ⊗_R ⋯ ⊗_R A ⊗_R M` *discharged* rather than hypothesised — the
`Γ ⊣ Spec` adjunction on the affine slice supplies it through
`Stacks.CechSite.isColimitPowerSectionsCoconeOfAdjunction`.

Both clauses of 03DW are therefore covered in every degree; the small *Zariski* half of clause
(2) is in
`StacksFrontier/AlgebraicGeometry/Topologies/Zariski/SmallZariskiQuasiCoherentCohomology.lean`.
The small Zariski half needs no affine vanishing at all: the comparison functor there
is an equivalence of sites, so the higher direct images vanish by
`CategoryTheory.Functor.isZero_rightDerived_of_isEquivalence`.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on each of the five big sites over `S` have a left exact sheafification:
`AlgebraicGeometry.BigFppfOver.hasSheafify_baseOverTopology`, under its older name.  It stays an
instance so that the statements below elaborate to the same terms as before. -/
alias hasSheafify_baseOverTopology_addCommGrpCat :=
  AlgebraicGeometry.BigFppfOver.hasSheafify_baseOverTopology

attribute [instance] hasSheafify_baseOverTopology_addCommGrpCat

/-- **The restriction of `𝓕^a` to the small Zariski site of `S` is `𝓕`, as abelian sheaves.**

For a quasi-coherent `𝒪_S`-module `𝓕` the unit of the associated-module adjunction of
`(Sch/S)_τ` is an isomorphism, by [Stacks, Tag 03DT]: the pullback-sections presheaf of a
quasi-coherent module is a sheaf for each of the five topologies.  This is that unit with its
module structures forgotten. -/
public noncomputable def baseAssociatedModuleAbelianSheafIso (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    (SheafOfModules.toSheaf S.ringCatSheaf).obj F ≅
      (SheafOfModules.toSheaf S.ringCatSheaf).obj
        ((baseRestrictModule B S hS τ).obj ((baseAssociatedModule B S hS τ).obj F)) :=
  (SheafOfModules.toSheaf S.ringCatSheaf).mapIso
    (@asIso _ _ _ _ _ (isIso_baseUnit_app B S hS τ F))

/-- **`Γ(U, 𝓕) = Γ(U, 𝓕^a)` for every open `U` of `S`.**

The sections of a quasi-coherent `𝒪_S`-module over an open `U` are the sections of its
associated module on `(Sch/S)_τ` over `U` viewed as an object of that site.  Restriction along
the inclusion of the small Zariski site is evaluation at the image object, so this is the
previous isomorphism evaluated at `U`. -/
public noncomputable def baseAssociatedModuleSectionsIso (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] (U : S.Opens) :
    ((SheafOfModules.toSheaf S.ringCatSheaf).obj F).obj.obj (op U) ≅
      ((SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj
          ((baseAssociatedModule B S hS τ).obj F)).obj.obj
        (op ((opensToBig B S hS).obj U)) :=
  ((sheafToPresheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u}).mapIso
    (baseAssociatedModuleAbelianSheafIso B S hS τ F)).app (op U)

/-- **`H^0(U, 𝓕) = H^0(U, 𝓕^a)` for every open `U` of `S`.**

Degree-zero sheaf cohomology over an object of a site is the group of sections over that object,
so this is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSectionsIso` read on cohomology. -/
public noncomputable def h'ZeroBaseAssociatedModuleAddEquiv (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (baseOverTopology B S hS τ) AddCommGrpCat.{u})] (U : S.Opens) :
    Sheaf.H'.{u} ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) 0 U ≃+
      Sheaf.H'.{u} ((SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj
        ((baseAssociatedModule B S hS τ).obj F)) 0 ((opensToBig B S hS).obj U) :=
  ((Stacks.Cohomology.FreeYoneda.extSectionsAddEquiv U
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj F)).trans
      (baseAssociatedModuleSectionsIso B S hS τ F U).addCommGroupIsoToAddEquiv).trans
    (Stacks.Cohomology.FreeYoneda.extSectionsAddEquiv ((opensToBig B S hS).obj U)
      ((SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj
        ((baseAssociatedModule B S hS τ).obj F))).symm

/-- **[Stacks, Tag 03DW], clause (1), in the case `q = 0`.**  Let `S` be a scheme, let `𝓕` be a
quasi-coherent `𝒪_S`-module and let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  There is a
canonical isomorphism

```
H^0(S, 𝓕)  =  H^0((Sch/S)_τ, 𝓕^a).
```

Cohomology of a site in degree zero is the group of global sections, that is the sections over a
terminal object; the open `⊤` of `S` is terminal both in the small Zariski site of `S` and, as an
object of the big site, in `(Sch/S)_τ`.  So the isomorphism is the identification
`Γ(S, 𝓕) = Γ(S, 𝓕^a)` of
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSectionsIso`, which is the unit of the
associated-module adjunction at a quasi-coherent module.

Only `q = 0` is asserted *by this declaration*, and only on this site: the big site here is
`AlgebraicGeometry.BigFppfOver.baseOverTopology`, five topologies on the one underlying
category of a chosen big fppf site.  Every degree `q`, on
`AlgebraicGeometry.overTopology`, is `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso`,
and clause (2) in its small étale half is
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`; both carry the tag.  For
`τ ≠ fppf` those two sites are topologies on different categories, so this declaration is not
subsumed by them and stays part of the covering set.  The small Zariski half of clause (2) is
`AlgebraicGeometry.smallZariskiQuasiCoherentGlobalCohomologyIso`
(`StacksFrontier/AlgebraicGeometry/Topologies/Zariski/SmallZariskiQuasiCoherentCohomology.lean`),
which carries the tag as well. -/
@[stacks 03DW "the case q = 0 of clause (1), for every one of the five topologies"]
public noncomputable def hZeroBaseAssociatedModuleAddEquiv (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf (baseOverTopology B S hS τ) AddCommGrpCat.{u})] :
    Sheaf.H.{w} ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) 0 ≃+
      Sheaf.H.{w} ((SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj
        ((baseAssociatedModule B S hS τ).obj F)) 0 :=
  ((Sheaf.H.equiv₀ ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) isTerminalTop).trans
      (baseAssociatedModuleSectionsIso B S hS τ F ⊤).addCommGroupIsoToAddEquiv).trans
    (Sheaf.H.equiv₀
      ((SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj
        ((baseAssociatedModule B S hS τ).obj F))
      (isTerminalOpensObjTop B S hS)).symm

end AlgebraicGeometry.BigFppfOver

end
