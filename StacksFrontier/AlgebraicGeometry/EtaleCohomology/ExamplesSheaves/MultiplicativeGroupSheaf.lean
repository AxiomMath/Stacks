module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ChosenFlatSiteSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ChosenSiteSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# `𝐆_m` on the big and small sites of a scheme

Let `S` be a scheme and let `τ ∈ {fppf, syntomic, smooth, étale, Zariski}`.  The second sheaf
named by [Stacks, Tag 03P4] is `T ↦ Γ(T, 𝒪_T^*)`, written `𝒪_S^*` or `𝐆_m` or `𝐆_{m,S}`.  This
module puts it on a site of schemes over `S` and then on each of the seven sites
`(Sch/S)_τ` and `S_τ` of [Stacks, Tag 03X7], with the sheaf condition discharged rather than
assumed.

The group law is multiplication of invertible functions, and the sheaf is recorded as an
abelian sheaf (`AddCommGrpCat`) through `AlgebraicGeometry.unitsPresheaf`, which is the shape
in which the rest of the chapter takes its cohomology and its Kummer sequences.

## Main definitions

* `Stacks.Sites.multiplicativeGroupPresheaf`: the presheaf `T ↦ (Γ(T, 𝒪_T)^*, ·)` on a site of
  schemes over `S`.
* `Stacks.Sites.multiplicativeGroupSheaf`: the same presheaf as an abelian sheaf, once the
  units of global functions are a sheaf of types on the site.
* `AlgebraicGeometry.BigFppfOver.multiplicativeGroupSheaf`,
  `AlgebraicGeometry.BigSyntomicOver.multiplicativeGroupSheaf`,
  `AlgebraicGeometry.BigSmoothOver.multiplicativeGroupSheaf`,
  `AlgebraicGeometry.BigEtaleOver.multiplicativeGroupSheaf`,
  `AlgebraicGeometry.BigZariskiOver.multiplicativeGroupSheaf`,
  `AlgebraicGeometry.SmallEtale.multiplicativeGroupSheaf`,
  `AlgebraicGeometry.SmallZariski.multiplicativeGroupSheaf`: `𝐆_m` on each of the seven sites
  `(Sch/S)_τ` and `S_τ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isSheaf_globalUnits` and its six companions, one per site: the
  units of global functions are a sheaf of types there.  Every one of the seven is the fpqc
  sheaf condition `Stacks.Sites.isSheaf_fpqcOver_globalUnits` restricted along the site's
  canonical functor, which is the route [Stacks, Tag 03O4] provides.

## Implementation notes

The sheaf condition for a presheaf of abelian groups is the sheaf condition for the underlying
presheaf of types, so each site's statement is obtained by restricting
`Stacks.Sites.isSheaf_fpqcOver_globalUnits` along the canonical functor of the site with the
appropriate member of the `AlgebraicGeometry.isSheaf_*_of_isSheaf_fpqc` family and transporting
the result back through `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`.  Nothing here uses
faithfully flat descent a second time: the fpqc sheaf condition itself holds because `𝐆_m` is
represented by the multiplicative group scheme over `S` and the fpqc topology is subcanonical.

The sites are the seven of [Stacks, Tag 03XB]: the big `τ`-site for each of the five topologies,
and the small `τ`-site for `τ ∈ {étale, Zariski}`, which are the only two for which
[Stacks, Tag 03XB] defines one.

## References

* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
* [Stacks Project, Tag 03X7](https://stacks.math.columbia.edu/tag/03X7)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
* [Stacks Project, Tag 03O4](https://stacks.math.columbia.edu/tag/03O4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Sites

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- **`𝐆_m` on a site of schemes over `S`.**  The presheaf of abelian groups whose sections
over an object `T/S` of the site are the invertible global functions `Γ(T, 𝒪_T^*)`.  It is the
presheaf of units of the structure presheaf of the site, recorded additively so that it is an
abelian presheaf. -/
@[sga "4 IX 3.0" "presheaf of sections Γ(U", sga "4½ Arcata 2.2.2"]
abbrev multiplicativeGroupPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  unitsPresheaf (toOver ⋙ Over.forget S)

/-- The multiplicative group presheaf of a site of schemes over `S` is a sheaf as soon as the
restriction to the site of the presheaf of types of invertible global functions is a sheaf: the
sheaf condition for a presheaf of abelian groups is the sheaf condition for its underlying
presheaf of types. -/
theorem isSheaf_multiplicativeGroupPresheaf (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalUnitsOver S)) :
    Presheaf.IsSheaf J (multiplicativeGroupPresheaf S toOver) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ (CategoryTheory.forget AddCommGrpCat) h

/-- **Stacks 03P4, part (2).**  `𝐆_m = 𝒪_S^*` as an abelian sheaf on a site of schemes over `S`
on which the invertible global functions are a sheaf of types. -/
@[stacks 03P4 "part (2), 𝐆_m on a site of schemes over S"]
def multiplicativeGroupSheaf (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalUnitsOver S)) :
    Sheaf J AddCommGrpCat.{u} :=
  ⟨multiplicativeGroupPresheaf S toOver, isSheaf_multiplicativeGroupPresheaf S toOver J h⟩

/-- The underlying presheaf of `𝐆_m` on a site of schemes over `S` is the presheaf of units of
global functions on the site. -/
@[simp, sga "4½ Arcata 2.2.2"]
theorem multiplicativeGroupSheaf_obj (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalUnitsOver S)) :
    (multiplicativeGroupSheaf S toOver J h).obj = unitsPresheaf (toOver ⋙ Over.forget S) :=
  rfl

end Stacks.Sites

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-! ### `𝐆_m` on the five big sites -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (hS : B.Contains S)

/-- Invertible global functions are a sheaf of types on the big fppf site over `S`. -/
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((Over.post (X := B.obj hS) B.inclusion).op ⋙ Stacks.Sites.globalUnitsOver S) :=
  isSheaf_bigFppf_of_isSheaf_fpqc B S hS _ (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the big fppf site.**  `𝐆_m` as an abelian sheaf on
`(Sch/S)_{fppf}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the big fppf site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S (Over.post (X := B.obj hS) B.inclusion)
    (topology B S hS) (isSheaf_globalUnits S B hS)

end BigFppfOver

namespace BigSyntomicOver

variable (B : BigSyntomicSite.{u}) (hS : B.Contains S)

/-- Invertible global functions are a sheaf of types on the big syntomic site over `S`. -/
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((Over.post (X := B.obj S hS) B.inclusion).op ⋙ Stacks.Sites.globalUnitsOver S) :=
  isSheaf_bigSyntomic_of_isSheaf_fpqc B S hS _ (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the big syntomic site.**  `𝐆_m` as an abelian sheaf on
`(Sch/S)_{syntomic}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the big syntomic site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S (Over.post (X := B.obj S hS) B.inclusion)
    (topology B S hS) (isSheaf_globalUnits S B hS)

end BigSyntomicOver

namespace BigSmoothOver

variable (B : BigSmoothSite.{u}) (hS : S.size < B.cutoff)

/-- Invertible global functions are a sheaf of types on the big smooth site over `S`. -/
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _)).op ⋙
        Stacks.Sites.globalUnitsOver S) :=
  isSheaf_bigSmooth_of_isSheaf_fpqc B S hS _ (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the big smooth site.**  `𝐆_m` as an abelian sheaf on
`(Sch/S)_{smooth}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the big smooth site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S
    (Over.post (X := (⟨S, hS⟩ : B.category)) (ObjectProperty.ι _)) (topology B S hS)
    (isSheaf_globalUnits S B hS)

end BigSmoothOver

namespace BigEtaleOver

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- Invertible global functions are a sheaf of types on the big étale site over `S`. -/
@[sga "4 IX 3.0" "partial"]
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((Over.post (X := B.obj S hS) B.inclusion).op ⋙ Stacks.Sites.globalUnitsOver S) :=
  isSheaf_chosenBigEtale_of_isSheaf_fpqc B S hS _ (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the big étale site.**  `𝐆_m` as an abelian sheaf on
`(Sch/S)_{étale}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the big étale site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S (Over.post (X := B.obj S hS) B.inclusion)
    (topology B S hS) (isSheaf_globalUnits S B hS)

end BigEtaleOver

namespace BigZariskiOver

variable (B : BigZariskiSite.{u}) (hS : B.Contains S)

/-- Invertible global functions are a sheaf of types on the big Zariski site over `S`. -/
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).op ⋙
        Stacks.Sites.globalUnitsOver S) :=
  isSheaf_bigZariski_of_isSheaf_fpqc B S hS _ (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the big Zariski site.**  `𝐆_m` as an abelian sheaf on
`(Sch/S)_{Zar}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the big Zariski site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S
    (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) (topology B S hS)
    (isSheaf_globalUnits S B hS)

end BigZariskiOver

/-! ### `𝐆_m` on the two small sites -/

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- Invertible global functions are a sheaf of types on the small étale site of `S`. -/
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion).op ⋙
        Stacks.Sites.globalUnitsOver S) :=
  isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS _
    (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the small étale site.**  `𝐆_m` as an abelian sheaf on
`S_{étale}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the small étale site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S
    (inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion) (topology B S hS)
    (isSheaf_globalUnits S B hS)

end SmallEtale

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (hS : B.Contains S)

/-- Invertible global functions are a sheaf of types on the small Zariski site of `S`. -/
theorem isSheaf_globalUnits :
    Presheaf.IsSheaf (topology B S hS)
      ((inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).op ⋙
        Stacks.Sites.globalUnitsOver S) :=
  isSheaf_smallZariski_of_isSheaf_fpqc B S hS _ (Stacks.Sites.isSheaf_fpqcOver_globalUnits S)

/-- **Stacks 03P4, part (2), the small Zariski site.**  `𝐆_m` as an abelian sheaf on
`S_{Zar}`. -/
@[stacks 03P4 "part (2), 𝐆_m on the small Zariski site"]
def multiplicativeGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.multiplicativeGroupSheaf S
    (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)
    (topology B S hS) (isSheaf_globalUnits S B hS)

end SmallZariski

end AlgebraicGeometry

end
