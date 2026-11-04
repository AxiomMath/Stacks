module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheafNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperFibrewiseVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `R^p π_* G = 0` for a proper map and a sheaf with soft restrictions to the fibres

`Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` proves that, for a closed map
`π : X ⟶ W` with quasi-compact fibres whose points are separated in `X` and an abelian sheaf `G`
on `X` whose restriction to every fibre is soft, every class in `H^p(π^{-1} V, G)` dies on a
covering sieve of `V` — where `H^p(U, -)` is the `Ext`-theoretic cohomology
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf` of
`DerivedSections/FreeYonedaSectionsUnivLE.lean`, the only one available with the coefficient
universe free of the space.

This file turns that into the vanishing of the higher direct image itself,

`R^p π_* G = 0` for `p > 0`,

through [Stacks, Tag 072W]: by
`Stacks.Cohomology.SheafifiedHigherDirectImage.isZero_rightDerived_pushforward_of_locallyZero`
it is enough that the sections of `((pushforwardCohomologyPresheaf _ (Opens.map π)).rightDerived
p).obj G` die locally, and by
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheafRestrictionIso` that
presheaf is the cohomology presheaf of the site of opens of `X`, restricted along
`Opens.map π`.

What the step costs is one **natural** identification of the two cohomology presheaves of a site:
`(sheafToPresheaf J AddCommGrpCat).rightDerived p` and the `Ext`-theoretic one. Naturality in the
object of the site is exactly what cannot be dispensed with here — the hypothesis of
`isZero_rightDerived_pushforward_of_locallyZero` is about restriction maps — and it is available
only with the coefficient universe pinned to the homs of the site: it is
`Stacks.Cohomology.rightDerivedSheafToPresheafIso`, the second half of [Stacks, Tag 03AY], stated
for a small site and `AddCommGrpCat.{u}`. Accordingly the theorems of this file fix the
coefficient universe to the universe of the space; see the implementation notes.

## Main results

* `Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafIsoPinned`: the freed cohomology presheaf
  at `t := v` is Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`, naturally in the object of
  the site. The objectwise statement is
  `Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoPinned`; what is added is the
  naturality, which comes from `Stacks.Cohomology.FreeYonedaUnivLE.freeYonedaIso` being an
  isomorphism of functors.
* `Stacks.Cohomology.FreeYonedaUnivLE.rightDerivedObjIsoCohomologyPresheafUnivLE`: on a small
  site, `((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj G` is the freed cohomology
  presheaf of `G`, naturally in the object of the site.
* `Stacks.Topology.isZero_rightDerived_pushforward_of_isSoft_fiber`: **`R^p π_* G = 0` for
  `p > 0`**, for a closed map with quasi-compact separated fibres and a sheaf whose restriction to
  every fibre is soft.
* `Stacks.Topology.isZero_rightDerived_pushforward_of_isFlasque`: the same for a flasque `G`.

## Implementation notes

The coefficient universe is the universe of the space. That is not where the derived clause of
[Stacks, Tag 0DCU] needs this statement: there the spaces lie in `TopCat.{u}` and the
coefficients are `AddCommGrpCat.{max (u + 1) v}`, and the whole `UnivLE` apparatus of
`CompactSubset/` exists in order to reach them. Every input of the argument *is* available at
those universes — `Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber`, which carries the
mathematics, is stated with `t` free — and the single thing that is not is the natural
identification above: `Stacks.Cohomology.rightDerivedSheafToPresheafIso` pins the coefficients to
the homs of the site, because
`Stacks.Cohomology.cohomologyPresheafIsoResolution` is built from
`Stacks.Cohomology.Locality.extEquivSectionHomology`, whose source and target categories must
share a `Type` universe. Freeing it is the mixed-universe generalisation that this file does not
carry out, and it is the one step between
`Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` and the vanishing of a higher direct image
at the universes of Tag 0DCU.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the
tag is not complete until all of them are in the library.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe uA vA u

section Pinned

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{u} A]

/-- Two factorisations of one morphism give the same precomposition on `Ext`. This is the
`Ext`-level content of the naturality square below; it is stated as a `have`-style congruence
because the two sides are composites of `Abelian.Ext.mk₀`, which no keyed rewrite reaches
through. -/
theorem mk₀_comp_mk₀_congr {P Q Q' R M : A} (f : P ⟶ Q) (g : Q ⟶ R) (f' : P ⟶ Q')
    (g' : Q' ⟶ R) (hfg : f ≫ g = f' ≫ g') {p : ℕ} (x : Abelian.Ext.{u} R M p) :
    (Abelian.Ext.mk₀ f).comp ((Abelian.Ext.mk₀ g).comp x (zero_add p)) (zero_add p) =
      (Abelian.Ext.mk₀ f').comp ((Abelian.Ext.mk₀ g').comp x (zero_add p)) (zero_add p) := by
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀_assoc, hfg]

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- **At `t := v` the freed cohomology presheaf is Mathlib's, naturally in the object of the
site.** `Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoPinned` is this isomorphism at
one object; the naturality added here is the naturality of
`Stacks.Cohomology.FreeYonedaUnivLE.freeYonedaIso`, which is an isomorphism of functors
`C ⥤ Sheaf J AddCommGrpCat`. -/
def cohomologyPresheafIsoPinned (G : Sheaf J AddCommGrpCat.{u}) (p : ℕ) :
    cohomologyPresheaf.{u, u} G p ≅ Sheaf.cohomologyPresheaf G p :=
  NatIso.ofComponents (fun U ↦ cohomologyPresheafObjIsoPinned J G p U.unop)
    (fun {_ _} a ↦ ConcreteCategory.hom_ext _ _ fun x ↦
      mk₀_comp_mk₀_congr _ _ _ _ ((freeYonedaIso.{u} J).inv.naturality a.unop).symm x)

/-- **On a small site the `p`-th right derived functor of the inclusion of sheaves into presheaves
is the freed cohomology presheaf**, naturally in the object of the site. This is the second half
of [Stacks, Tag 03AY], `Stacks.Cohomology.rightDerivedSheafToPresheafIso`, read in the cohomology
presheaf of `DerivedSections/FreeYonedaSectionsUnivLE.lean` through
`cohomologyPresheafIsoPinned`. -/
@[sga "4 IV 4.8" "for an abelian sheaf G", sga "4 V 2.4.2" "(2.4.2.2), special case"]
def rightDerivedObjIsoCohomologyPresheafUnivLE (G : Sheaf J AddCommGrpCat.{u})
    (p : ℕ) :
    ((sheafToPresheaf J AddCommGrpCat.{u}).rightDerived p).obj G ≅
      cohomologyPresheaf.{u, u} G p :=
  (Stacks.Cohomology.rightDerivedSheafToPresheafIso J p).app G ≪≫
    (cohomologyPresheafIsoPinned J G p).symm

end Pinned

end Stacks.Cohomology.FreeYonedaUnivLE

namespace Stacks.Topology

universe s

variable {X W : TopCat.{s}} (π : X ⟶ W)
  (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{s})

/-- **`R^p π_* G = 0` for `p > 0`, for a closed map with quasi-compact separated fibres and a
sheaf whose restriction to every fibre is soft.**

This is `Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` fed into [Stacks, Tag 072W]: the
higher direct image is the sheafification of the cohomology presheaf of the source site restricted
along `Opens.map π`, and every section of that presheaf dies on a covering sieve. The coefficient
universe is the universe of the space, because the natural identification of the two cohomology
presheaves of a site is available only there; see the implementation notes of this file. -/
@[sga "4 V 4.13" "special case", sga "6 II 2.3.1" "partial"]
theorem isZero_rightDerived_pushforward_of_isSoft_fiber
    (hcl : IsClosedMap (π.hom : X → W))
    (hcpt : ∀ w : W, IsCompact ((π.hom : X → W) ⁻¹' ({w} : Set W)))
    (hsep : IsSeparatedMap (π.hom : X → W))
    (hsoft : ∀ w : W, IsSoft ((restrictionFunctorUnivLE.{s} X
      ((π.hom : X → W) ⁻¹' ({w} : Set W))).obj G))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((Opens.map π).sheafPushforwardContinuous AddCommGrpCat.{s}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology X)).rightDerived p).obj G) := by
  let _hei : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{s}) :=
    enoughInjectives_sheafOpens.{s} X
  let _hext : HasExt.{s} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{s}) :=
    hasExt_sheafOpens.{s} X
  refine isZero_rightDerived_pushforward_of_locallyZero
    (J := Opens.grothendieckTopology W) (K := Opens.grothendieckTopology X)
    (Opens.map π) p G fun V ξ ↦ ?_
  refine equalizerSieve_mem_of_presheafIso (Opens.grothendieckTopology W)
    ((pushforwardCohomologyPresheafRestrictionIso AddCommGrpCat.{s} (Opens.map π) p).app G ≪≫
      Functor.isoWhiskerLeft (Opens.map π).op
        (Stacks.Cohomology.FreeYonedaUnivLE.rightDerivedObjIsoCohomologyPresheafUnivLE
          (Opens.grothendieckTopology X) G p))
    (fun V' ξ' ↦ equalizerSieve_mem_of_isSoft_fiber.{s} G π hcl hcpt hsep hsoft p hp V' ξ') V ξ

/-- **`R^p π_* G = 0` for `p > 0` and `G` flasque**, for a closed map with quasi-compact fibres
whose points are separated in the source. The restriction of a flasque sheaf to a quasi-compact
subset with separated points is soft
(`Stacks.Topology.isSoft_restrictionFunctorUnivLE_of_isFlasque`), so the fibrewise hypothesis of
`isZero_rightDerived_pushforward_of_isSoft_fiber` is automatic. -/
theorem isZero_rightDerived_pushforward_of_isFlasque [TopCat.Sheaf.IsFlasque G]
    (hcl : IsClosedMap (π.hom : X → W))
    (hcpt : ∀ w : W, IsCompact ((π.hom : X → W) ⁻¹' ({w} : Set W)))
    (hsep : IsSeparatedMap (π.hom : X → W))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((Opens.map π).sheafPushforwardContinuous AddCommGrpCat.{s}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology X)).rightDerived p).obj G) := by
  refine isZero_rightDerived_pushforward_of_isSoft_fiber π G hcl hcpt hsep (fun w ↦ ?_) p hp
  refine isSoft_restrictionFunctorUnivLE_of_isFlasque.{s} G _ (hcpt w) ?_
  intro x hx y hy hxy
  refine hsep x y ?_ hxy
  have hx' : (π.hom : X → W) x = w := hx
  have hy' : (π.hom : X → W) y = w := hy
  rw [hx', hy']

end Stacks.Topology

end
