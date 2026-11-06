module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeRows
public import StacksFrontier.Cotangent.BaseChangeQuasiIso
public import StacksFrontier.Cotangent.PolynomialAlgebraSitePointValuesLargeSite

/-!
# `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A})` at the site `C_{B/A}` itself

Let `A → B` be a ring map and let `π`, `𝒪`, `B̲` be as in [Stacks, Tag 08PR]. The last
identification of [Stacks, Tag 08QK] is

```
Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A})      in `D(Ab)`.
```

This file proves it **at `CommAlgCat.polynomialSite` itself** -- the site of [Stacks, Tag 08PR],
not a restriction of it and not a small model of it -- for the sheaf of relative differentials
`CommAlgCat.polynomialRelativeDifferentials` of that site and its own base change
`CommAlgCat.polynomialRelativeDifferentialsBaseChange` along the augmentation `𝒪 ⟶ B̲`, with no
hypothesis on `A → B`.

## Main results

* `CommAlgCat.polynomialSiteDerivedLowerShriekDifferentialsBaseChangeIso`:
  **`Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`** in `D(Ab)`, as the isomorphism induced by the
  base-change unit `Ω_{𝒪/A} ⟶ Ω_{𝒪/A} ⊗_𝒪 B̲`.
* `CommAlgCat.quasiIso_mooreCochain_polynomialSiteDifferentialsBaseChangeUnit`: the
  quasi-isomorphism of Moore complexes that the criterion of [Stacks, Tag 08Q9] asks for.

## Implementation notes

**The route avoids [Stacks, Tag 08QJ].** The source deduces this identification from Tag 08QJ at
`ℱ = Ω_{𝒪/A}`, whose dévissage -- [Stacks, Tag 08RX] at a general site -- is proved in this library
only for a site that is a `SmallCategory` with coefficients in `RingCat.{u}`:
`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single` and every link of its chain,
through `Stacks.ChaoticSite.changeOfRingsAdjunction`,
`Stacks.ChaoticSite.derivedColimitTensorComparison` and
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero`. The objects of `C_{B/A}` live
one universe above its morphisms, so none of those apply.

What is used instead is the **Δ-instance** of Tag 08RX,
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app`: for a simplicial commutative ring
`O`, a homomorphism `φ : O ⟶ O'` whose underlying map of Moore complexes is a
quasi-isomorphism, and a simplicial `O`-module flat in every simplicial degree, the base-change
unit `s(M) ⟶ s(M ⊗_O O')` is a quasi-isomorphism. That statement mentions no site and no
smallness, and **its universe is free**, so it applies at `u + 1`, the coefficient universe of
`C_{B/A}`. Composed with
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large` -- the
criterion of [Stacks, Tag 08Q9] on a single morphism with no smallness hypothesis -- it gives the
identification directly.

**Why no universe bookkeeping enters.** Because the Δ-instance is applied at `u + 1`, the
simplicial ring in play is `𝒪(P_•, ε)`, the site's own structure sheaf evaluated on the standard
resolution, whose sections are `ULift P_n`; and the simplicial module is `Ω_{𝒪/A}(P_•, ε)`, whose
sections are `Ω[ULift P_n⁄ULift A]`. No `Type u` model of either is needed, and the only fact
about the universe lift that is consumed is the one already in the tree:
`KaehlerDifferential.flat_ulift_of_free`, which is exactly the degreewise flatness hypothesis.

**The restriction to `Δ` is an equality.** Evaluating Mathlib's presheaf of relative differentials
on a cosimplicial object returns the presheaf of relative differentials of the evaluated map of
presheaves of rings, on the nose: both send `n` to the Kähler differentials of the map at `U_n`
and both have `CommRingCat.KaehlerDifferential.map` for restriction maps. That is
`CommAlgCat.resolutionPolynomialSiteDifferentials`, and it is what lets the base-change unit at
the site be read as the base-change unit on `Δ` with no comparison map
(`CommAlgCat.mooreCochainComplex_map_polynomialSiteDifferentialsBaseChangeUnit`).

## References

* [Stacks Project, Tag 08QK](https://stacks.math.columbia.edu/tag/08QK)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The structure sheaf and `Ω_{𝒪/A}` restricted to the standard resolution -/

/-- `𝒪(P_•, ε)`: the structure sheaf of [Stacks, Tag 08PR] evaluated on the cosimplicial object
of the standard resolution, as a simplicial commutative ring. Its sections in simplicial degree
`n` are `ULift P_n`. -/
abbrev resolutionPolynomialSiteRing : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
    (polynomialStructureSheaf A B).obj

/-- The augmentation `𝒪 ⟶ B̲` of [Stacks, Tag 08PR] evaluated on the cosimplicial object of the
standard resolution, as a homomorphism of simplicial commutative rings. -/
abbrev resolutionPolynomialSiteAug :
    resolutionPolynomialSiteRing A B ⟶
      (standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
        (polynomialConstantSheaf A B).obj :=
  Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
    (polynomialAugmentation A B).hom

/-- **`Ω_{𝒪/A}(P_•, ε)`: the sheaf of relative differentials of `C_{B/A}` evaluated on the
cosimplicial object of the standard resolution, as a simplicial module over `𝒪(P_•, ε)`.**

No comparison map intervenes. Mathlib's `relativeDifferentials'` sends `V` to the Kähler
differentials of `A̲ ⟶ 𝒪` at `V` and a morphism to `CommRingCat.KaehlerDifferential.map` of the
naturality square, so restricting it along a functor returns the presheaf of relative
differentials of the restricted map of presheaves of rings, on the nose. -/
abbrev resolutionPolynomialSiteDifferentials :
    Stacks.SimplicialModules.SMod (resolutionPolynomialSiteRing A B) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
      (polynomialBaseStructureHom A B).hom)

/-- **The sections of `Ω_{𝒪/A}(P_•, ε)` are flat over `𝒪(P_•, ε)` in every simplicial degree.**
The term `P_n` of the standard resolution is a polynomial algebra over `A`, so `Ω[P_n⁄A]` is a
free `P_n`-module (`CommAlgCat.free_kaehlerDifferential_standardResolution`), and
`KaehlerDifferential.flat_ulift_of_free` carries that to the flatness of
`Ω[ULift P_n⁄ULift A]` over `ULift P_n` for the algebra structure the lifted structure map
induces -- which is the one the sections of `Ω_{𝒪/A}` carry, by
`CommAlgCat.polynomialBaseStructureHom_app`.

This is the degreewise flatness hypothesis of the Δ-instance of [Stacks, Tag 08RX]. -/
theorem flat_resolutionPolynomialSiteDifferentials (n : SimplexCategoryᵒᵖ) :
    Module.Flat ↥((Stacks.ringPresheaf (resolutionPolynomialSiteRing A B)).obj n)
      ↥((resolutionPolynomialSiteDifferentials A B).obj n) :=
  KaehlerDifferential.flat_ulift_of_free.{u, u + 1} A
    ((standardResolution.{u, u} A B).left.obj n : Type u)
    (free_kaehlerDifferential_standardResolution A B n)

/-! ### The augmentation `𝒪 ⟶ B̲` on the Moore complex of the resolution -/

/-- The augmentation of sheaves of rings of [Stacks, Tag 08PR] is the augmentation of presheaves
followed by the identification of the constant sheaf with the constant presheaf. -/
lemma polynomialAugmentation_hom_eq :
    (polynomialAugmentation A B).hom =
      polynomialAugmentationPresheaf A B ≫ (polynomialConstantSheafIso A B).inv :=
  (fullyFaithfulSheafToPresheaf (polynomialTopology A B) CommRingCat.{u + 1}).map_preimage _

/-- **The augmentation `𝒪(P_•, ε) ⟶ B̲(P_•, ε)` read on the underlying simplicial abelian
groups is `CommAlgCat.polynomialSiteAbelianAugmentation` evaluated on the resolution,
followed by an isomorphism.** The isomorphism is
`CommAlgCat.polynomialConstantSheafIso`, by which the constant sheaf of rings of
[Stacks, Tag 08PF] is the constant presheaf with value `B`; that augmentation is the one
into the constant presheaf, and `Stacks.PresheafOfModules.ChangeOfRings.unitMap'` of either is the
ring map read additively, so the comparison is an equality of natural transformations. -/
lemma unitMap_resolutionPolynomialSiteAug_eq :
    unitMap' (resolutionPolynomialSiteAug A B) =
      Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
          (polynomialSiteAbelianAugmentation A B) ≫
        unitMap' (Functor.whiskerLeft
          (standardResolutionPolynomialSiteCosimplicialObject A B).op
          (polynomialConstantSheafIso A B).inv) := by
  rw [show resolutionPolynomialSiteAug A B =
      Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
        (polynomialAugmentationPresheaf A B ≫ (polynomialConstantSheafIso A B).inv) from
    congrArg _ (polynomialAugmentation_hom_eq A B)]
  rfl

/-- A componentwise isomorphism of presheaves of commutative rings, read additively by
`Stacks.PresheafOfModules.ChangeOfRings.unitMap'`, is an isomorphism: each component is a
bijection. -/
instance isIso_unitMap_whiskerLeft_polynomialConstantSheafIso_inv :
    IsIso (unitMap' (Functor.whiskerLeft
      (standardResolutionPolynomialSiteCosimplicialObject A B).op
      (polynomialConstantSheafIso A B).inv)) := by
  have happ : ∀ n : SimplexCategoryᵒᵖ,
      IsIso ((unitMap' (Functor.whiskerLeft
        (standardResolutionPolynomialSiteCosimplicialObject A B).op
        (polynomialConstantSheafIso A B).inv)).app n) := by
    intro n
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso
      ((polynomialConstantSheafIso A B).inv.app
        ((standardResolutionPolynomialSiteCosimplicialObject A B).op.obj n))
  exact NatIso.isIso_of_isIso_app _

/-- **The augmentation `𝒪 ⟶ B̲` evaluated on the standard resolution is a quasi-isomorphism of
Moore complexes**, in the spelling the Δ-instance of [Stacks, Tag 08RX] asks for. This is
`CommAlgCat.quasiIso_mooreCochain_polynomialSiteAbelianAugmentation`, whose own input is
[Stacks, Tag 08QI], composed with an isomorphism. -/
theorem quasiIso_unitMap_resolutionPolynomialSiteAug :
    QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).map
      (unitMap' (resolutionPolynomialSiteAug A B))) := by
  set e := (alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).mapIso
    (asIso (unitMap' (Functor.whiskerLeft
      (standardResolutionPolynomialSiteCosimplicialObject A B).op
      (polynomialConstantSheafIso A B).inv))) with he
  have hmap : (alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).map
        (unitMap' (resolutionPolynomialSiteAug A B)) =
      (alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).map
          (Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
            (polynomialSiteAbelianAugmentation A B)) ≫ e.hom :=
    (congrArg (alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).map
      (unitMap_resolutionPolynomialSiteAug_eq A B)).trans (Functor.map_comp _ _ _)
  have harr : Arrow.mk ((alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).map
        (unitMap' (resolutionPolynomialSiteAug A B))) ≅
      Arrow.mk ((alternatingFaceMapCochainComplex AddCommGrpCat.{u + 1}).map
        (Functor.whiskerLeft (standardResolutionPolynomialSiteCosimplicialObject A B).op
          (polynomialSiteAbelianAugmentation A B))) :=
    Arrow.isoMk (Iso.refl _) e.symm
      (Eq.trans (Category.id_comp _) ((Iso.eq_comp_inv e).2 hmap.symm))
  exact (quasiIso_iff_of_arrow_mk_iso _ _ harr).2
    (quasiIso_mooreCochain_polynomialSiteAbelianAugmentation A B)

/-! ### `Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` -/

section Shriek

attribute [local instance] HasDerivedCategory.standard

/-- **`Ω_{𝒪/A}` read on its underlying abelian presheaf.** This is the sheaf of relative
differentials of [Stacks, Tag 08PR]'s site, `CommAlgCat.polynomialRelativeDifferentials`, read on
abelian groups so that `Lπ_!` of [Stacks, Tag 08Q6] can be applied to it. -/
abbrev polynomialSiteAbelianRelativeDifferentials :
    (polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (PresheafOfModules.toPresheaf (polynomialStructureRingSheaf A B).obj).obj
    (polynomialRelativeDifferentials A B).val

/-- **`Ω_{𝒪/A} ⊗_𝒪 B̲` read on its underlying abelian presheaf**, for the base change
`CommAlgCat.polynomialRelativeDifferentialsBaseChange` of `Ω_{𝒪/A}` along the augmentation
`𝒪 ⟶ B̲` of [Stacks, Tag 08PR]. -/
abbrev polynomialSiteAbelianDifferentialsBaseChange :
    (polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (PresheafOfModules.toPresheaf (polynomialConstantRingSheaf A B).obj).obj
    (polynomialRelativeDifferentialsBaseChangePresheaf A B)

/-- **The base-change unit `Ω_{𝒪/A} ⟶ Ω_{𝒪/A} ⊗_𝒪 B̲` as a map of sheaves of `𝒪`-modules**: the
unit of the change-of-rings adjunction along the augmentation `𝒪 ⟶ B̲` of [Stacks, Tag 08PR],
which on sections over `(P, α)` is `ω ↦ 1 ⊗ ω`. The target is the base change
`CommAlgCat.polynomialRelativeDifferentialsBaseChange` with its scalars restricted back to
`𝒪`. -/
def polynomialSiteDifferentialsBaseChangeUnitModule :
    (polynomialRelativeDifferentials A B).val ⟶
      (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars
          (polynomialAugmentation A B).hom).obj
        (polynomialRelativeDifferentialsBaseChangePresheaf A B) :=
  (changeOfRingsAdjunction.{u + 1, u, u + 1, u + 1}
    (polynomialAugmentation A B).hom).unit.app _

/-- **The base-change unit `Ω_{𝒪/A} ⟶ Ω_{𝒪/A} ⊗_𝒪 B̲`**, read on the underlying abelian
presheaves. Restriction of scalars does not change the underlying presheaf of abelian groups, so
the target is read at `B̲`. -/
def polynomialSiteDifferentialsBaseChangeUnit :
    polynomialSiteAbelianRelativeDifferentials A B ⟶
      polynomialSiteAbelianDifferentialsBaseChange A B :=
  (PresheafOfModules.toPresheaf (polynomialStructureRingSheaf A B).obj).map
    (polynomialSiteDifferentialsBaseChangeUnitModule A B)

/-- **The base-change unit of the site, evaluated on the standard resolution, is the base-change
unit on `Δ`** of the Δ-instance of [Stacks, Tag 08RX], on the nose. Both are the unit of the
change-of-rings adjunction read on underlying presheaves of abelian groups and then on Moore
complexes, and the restriction of `Ω_{𝒪/A}` along the cosimplicial object of the resolution is
`CommAlgCat.resolutionPolynomialSiteDifferentials` by definition. -/
lemma mooreCochainComplex_map_polynomialSiteDifferentialsBaseChangeUnit :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
        (standardResolutionPolynomialSiteCosimplicialObject A B)
        AddCommGrpCat.{u + 1}).map (polynomialSiteDifferentialsBaseChangeUnit A B) =
      (Stacks.SimplicialModules.mooreCochainBaseChange'
        (resolutionPolynomialSiteAug A B)).app
        (resolutionPolynomialSiteDifferentials A B) :=
  rfl

/-- **The base-change unit `Ω_{𝒪/A} ⟶ Ω_{𝒪/A} ⊗_𝒪 B̲` becomes a quasi-isomorphism on the
extended Moore complex of its evaluation on the standard resolution.**

This is the hypothesis in which the criterion of [Stacks, Tag 08Q9] asks for
`Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`, and it is the Δ-instance of [Stacks, Tag 08RX] --
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app`, which mentions no site and whose
universe is free -- applied at `u + 1` to the simplicial ring `𝒪(P_•, ε)`, the simplicial module
`Ω_{𝒪/A}(P_•, ε)` and the augmentation `𝒪(P_•, ε) ⟶ B̲(P_•, ε)`. Its two hypotheses are
`CommAlgCat.flat_resolutionPolynomialSiteDifferentials`, which is
`KaehlerDifferential.flat_ulift_of_free` at a term of the standard resolution, and
`CommAlgCat.quasiIso_unitMap_resolutionPolynomialSiteAug`, which is [Stacks, Tag 08QI].

No comparison map intervenes: the restriction of `Ω_{𝒪/A}` to the cosimplicial object of the
resolution *is* `CommAlgCat.resolutionPolynomialSiteDifferentials`, both being Mathlib's presheaf
of relative differentials of the same map of presheaves of rings. -/
theorem quasiIso_mooreCochain_polynomialSiteDifferentialsBaseChangeUnit :
    QuasiIso ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
      (standardResolutionPolynomialSiteCosimplicialObject A B)
      AddCommGrpCat.{u + 1}).map (polynomialSiteDifferentialsBaseChangeUnit A B)) := by
  rw [mooreCochainComplex_map_polynomialSiteDifferentialsBaseChangeUnit A B]
  exact Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app
    (resolutionPolynomialSiteAug A B)
    (resolutionPolynomialSiteDifferentials A B)
    (flat_resolutionPolynomialSiteDifferentials A B)
    (quasiIso_unitMap_resolutionPolynomialSiteAug A B)

/-- **`Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` in `D(Ab)` at the site `C_{B/A}` itself**, the last
identification of [Stacks, Tag 08QK], as the isomorphism **induced by the base-change unit**
`Ω_{𝒪/A} ⟶ Ω_{𝒪/A} ⊗_𝒪 B̲`.

Here `Ω_{𝒪/A}` is the sheaf of relative differentials of [Stacks, Tag 08PR]'s site, read on its
underlying abelian sheaf, `Ω_{𝒪/A} ⊗_𝒪 B̲` is its base change along the augmentation `𝒪 ⟶ B̲` of
that tag, `π` is the point morphism of the site `C_{B/A}` -- not of a restriction of it -- and
`Lπ_!` is the total left derived functor of the colimit over the index category, which is the
`π_!` of [Stacks, Tag 08PF]. There is no hypothesis on `A → B` beyond its being a ring map, and no
cardinal bound on the sets of variables.

The two inputs are the criterion of [Stacks, Tag 08Q9] with no smallness hypothesis on the site,
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large`, and the
quasi-isomorphism of Moore complexes
`CommAlgCat.quasiIso_mooreCochain_polynomialSiteDifferentialsBaseChangeUnit`, which is the
Δ-instance of [Stacks, Tag 08RX] rather than [Stacks, Tag 08QJ]. -/
@[stacks 08QK "Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A}) in D(Ab), as the isomorphism induced by \
  the base-change unit Ω_{𝒪/A} ⟶ Ω_{𝒪/A} ⊗_𝒪 B̲, for the point morphism of the site C_{B/A} of \
  Tag 08PR itself -- not of the footnote-restricted site nor of a small model of it -- with \
  Ω_{𝒪/A} the sheaf of relative differentials of that site and Ω_{𝒪/A} ⊗_𝒪 B̲ its base change \
  along the augmentation 𝒪 ⟶ B̲ of Tag 08PR, under no hypothesis on A → B and no cardinal bound"]
def polynomialSiteDerivedLowerShriekDifferentialsBaseChangeIso :
    polynomialSiteDerivedLowerShriekSingle A B
        (polynomialSiteAbelianRelativeDifferentials A B) ≅
      polynomialSiteDerivedLowerShriekSingle A B
        (polynomialSiteAbelianDifferentialsBaseChange A B) :=
  haveI : IsIso ((polynomialSiteAbelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (polynomialSiteDifferentialsBaseChangeUnit A B)))) :=
    (Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large
        (standardResolutionPolynomialSiteCosimplicialObject A B)
        (isPointResolution_standardResolutionPolynomialSiteCosimplicialObject A B) _).2
      (quasiIso_mooreCochain_polynomialSiteDifferentialsBaseChangeUnit A B)
  asIso ((polynomialSiteAbelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (polynomialSiteDifferentialsBaseChangeUnit A B))))

end Shriek

end CommAlgCat

end
