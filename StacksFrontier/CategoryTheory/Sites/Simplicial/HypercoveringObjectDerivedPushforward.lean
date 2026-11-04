module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismDerivedPushforward

/-!
# The derived direct image along the augmentation of a simplicial semi-representable object
over an object

Let `(C, J)` be a site with fibre products, let `X` be an object of `C` and let `K` be a
simplicial object of `SR(C, X) = FormalCoproduct (Over X)`. Replacing `C` by the slice site
`C/X` everywhere in the simplicial-site apparatus of Stacks 0D8B gives the simplicial family of
sites `n ↦ (C/X)/K_n`, its total site `(C/K)_total`, and the augmentation
`a : Sh((C/K)_total) ⟶ Sh(C/X)` whose inverse image is restriction along the localization
functor `j_total : (C/K)_total ⥤ C/X`.

This file carries that augmentation to abelian sheaves and derives it: it constructs
`a^{-1} : Ab(C/X) ⥤ Ab((C/K)_total)` and `a_*` with their adjunction, the unbounded derived
functors `a^{-1}` and `Ra_*`, and the canonical map

`E ⟶ Ra_* a^{-1} E`

for `E` in `D(C/X)`. The map is descended from the adjunction unit through the universal
property of the localization, so it is the canonical map and not a chosen one. Nothing here
constrains `K`: the augmentation, its derived functors and the canonical map exist for every
simplicial semi-representable object over `X`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.abelianTotalInverseImageOver` and
  `.abelianTotalPushforwardOver`: `a^{-1}` and `a_*` on abelian sheaves, with
  `.abelianTotalAdjunctionOver` the adjunction `a^{-1} ⊣ a_*`.
* `CategoryTheory.SimplicialSemiRepresentable.derivedAbelianTotalPushforwardOver`: `Ra_*`, the
  total right derived functor of `a_*` on unbounded derived categories, with
  `.derivedAbelianTotalPushforwardOverUnit` its canonical comparison.
* `CategoryTheory.SimplicialSemiRepresentable.derivedAbelianTotalInverseImageOver`: `a^{-1}` on
  unbounded derived categories, induced degreewise because `a^{-1}` is exact.
* `CategoryTheory.SimplicialSemiRepresentable.derivedAugmentationUnitOver`: the canonical map
  `E ⟶ Ra_* a^{-1} E` on `D(C/X)`, and `.derivedAugmentationUnitOverQh` the composite on
  unbounded homotopy categories which it descends from.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver`: `Ra_*` exists, with no
  hypothesis on `K`, because abelian sheaves on the total site are Grothendieck abelian and so
  admit K-injective resolutions.
* `CategoryTheory.SimplicialSemiRepresentable.whiskerLeft_derivedAugmentationUnitOver`: the
  canonical map restricted along the localization `Qh` is the composite it was descended from.
  This is what pins it down.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitOver_iff`: the
  canonical map is invertible exactly when that composite is, so invertibility may be tested on
  complexes.
* `CategoryTheory.SimplicialSemiRepresentable.derivedAugmentationUnitOverQh_app`: at a complex
  `M` the composite factors as the localization of the ordinary augmentation unit of `M`,
  followed by the comparison of `a_*` with `Ra_*` at `a^{-1}M`, followed by an isomorphism.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitOver_app`:
  **Stacks 0D8L**, granted its two inputs — the canonical map is invertible at every object of
  `D(C/X)` as soon as, at every complex, the ordinary augmentation unit is invertible and
  `a^{-1}` of that complex is computed by `a_*` rather than only by `Ra_*`. Both are carried as
  hypotheses; see the implementation notes.

## Implementation notes

The hypothesis that `C` has fibre products is the `HasPullbacks C` instance. It is what makes
`Over X` have pullbacks, hence makes the localized topology `J.over X` admit pullbacks of
coverings, which is what the simplicial family of sites of Stacks 0D8B requires; it is used for
nothing else here.

`a_*` is the direct image along the cocontinuous functor `j_total`, and `a^{-1}` is restriction
along the same functor, which is also continuous; this is the pair carried by
`CategoryTheory.SimplicialSemiRepresentable.totalLocalizationMorphism` of Stacks 0D8B on
sheaves of sets, taken at abelian coefficients. The adjunction is Stacks 00XL, so the unit below
is the one of that adjunction and not a transport of another.

`a^{-1}` is exact — it preserves finite limits because it is restriction along a continuous
functor, and all colimits because it is a left adjoint — so its derived functor is induced
degreewise and no derivation is needed on that side. `a_*` is only additive, and is derived.

The two inputs isolated by `isIso_derivedAugmentationUnitOver_app` are the two steps of the
source's argument, and neither is available in this library. The first, that the ordinary unit
`F ⟶ a_* a^{-1} F` is invertible, is the degree-zero half of Stacks 0D8K, carried in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDescent.lean` only granted local
fullness of `j_total`. The second, that `a^{-1}` of a K-injective complex is computed by `a_*`
with no higher direct images, is the vanishing of `R^p a_* a^{-1} I` in positive degrees; the
spectral sequence of Stacks 0D7A which computes those terms is not known to converge here,
because positive-degree exactness of the complex of Stacks 0D79 rests on the resolution of
Stacks 0D78, itself available only granted an undischarged hypothesis. Accordingly the
invertibility asserted by Stacks 0D8L is stated with those two inputs as explicit hypotheses,
and the attribute it carries names them; no unconditional invertibility is claimed anywhere
here. The absolute form of the same assertion, Stacks 0D8G, is carried in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCohomologicalDescent.lean` granted the
corresponding inputs for a site, so chaining to it would relocate these hypotheses rather than
discharge them.

The derived categories are the standard ones, `CategoryTheory.HasDerivedCategory.standard`,
installed as a local instance as in the neighbouring files so that no choice of model leaks out
of this module.

## References

* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-! ### The augmentation on abelian sheaves -/

/-- Abelian sheaves on the slice site `C/X`. -/
abbrev AbelianSheavesOver := Sheaf (J.over X) Ab.{u}

/-- Abelian sheaves on the total site `(C/K)_total` of a simplicial semi-representable object
over `X`. -/
abbrev TotalAbelianSheavesOver :=
  Sheaf ((situation (J.over X) K).totalTopology) Ab.{u}

/-- The inverse image `a^{-1} : Ab(C/X) ⥤ Ab((C/K)_total)` of the augmentation: restriction
along the localization functor `j_total`, which is continuous. -/
abbrev abelianTotalInverseImageOver :
    AbelianSheavesOver J X ⥤ TotalAbelianSheavesOver J X K :=
  (totalForget K).sheafPushforwardContinuous Ab.{u}
    ((situation (J.over X) K).totalTopology) (J.over X)

/-- The direct image `a_* : Ab((C/K)_total) ⥤ Ab(C/X)` of the augmentation: the direct image
along the localization functor `j_total`, which is cocontinuous. -/
abbrev abelianTotalPushforwardOver :
    TotalAbelianSheavesOver J X K ⥤ AbelianSheavesOver J X :=
  (totalForget K).sheafPushforwardCocontinuous Ab.{u}
    ((situation (J.over X) K).totalTopology) (J.over X)

/-- **Stacks 00XL** for the augmentation, on abelian sheaves: the inverse image is left adjoint
to the direct image. -/
def abelianTotalAdjunctionOver :
    abelianTotalInverseImageOver J X K ⊣ abelianTotalPushforwardOver J X K :=
  (totalForget K).sheafAdjunctionCocontinuous Ab.{u}
    ((situation (J.over X) K).totalTopology) (J.over X)

/-- The direct image `a_*` on abelian sheaves is additive, being a right adjoint between abelian
categories. -/
theorem additive_abelianTotalPushforwardOver :
    (abelianTotalPushforwardOver J X K).Additive :=
  additive_sheafPushforwardCocontinuous_ab _ _ (totalForget K)

attribute [local instance] additive_abelianTotalPushforwardOver

/-- The inverse image `a^{-1}` on abelian sheaves is additive, being a left adjoint. -/
theorem additive_abelianTotalInverseImageOver :
    (abelianTotalInverseImageOver J X K).Additive :=
  (abelianTotalAdjunctionOver J X K).left_adjoint_additive

/-- The inverse image `a^{-1}` preserves finite limits, being restriction along a continuous
functor. -/
instance preservesFiniteLimits_abelianTotalInverseImageOver :
    PreservesFiniteLimits (abelianTotalInverseImageOver J X K) :=
  Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ (totalForget K) Ab.{u}

/-- The inverse image `a^{-1}` preserves finite colimits, being a left adjoint. Together with
the previous instance this says `a^{-1}` is exact. -/
theorem preservesFiniteColimits_abelianTotalInverseImageOver :
    PreservesFiniteColimits (abelianTotalInverseImageOver J X K) :=
  letI := (abelianTotalAdjunctionOver J X K).leftAdjoint_preservesColimits
  inferInstance

attribute [local instance] additive_abelianTotalInverseImageOver
  preservesFiniteColimits_abelianTotalInverseImageOver

/-! ### The derived functors -/

/-- The direct image `a_*` applied degreewise, followed by localization: a right derived functor
of this functor is `Ra_*`. -/
abbrev homotopyAbelianTotalPushforwardOver :
    HomotopyCategory (TotalAbelianSheavesOver J X K) (ComplexShape.up ℤ) ⥤
      DerivedCategory (AbelianSheavesOver J X) :=
  (abelianTotalPushforwardOver J X K).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image along the augmentation pointwise.
Abelian sheaves on the total site form a Grothendieck abelian category, so every complex admits
a quasi-isomorphism into a K-injective one. -/
theorem hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver :
    (homotopyAbelianTotalPushforwardOver J X K).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (TotalAbelianSheavesOver J X K) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    Stacks.Cohomology.Localization.enoughKInjectives).1

attribute [local instance] hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

/-- **The derived direct image `Ra_*` along the augmentation exists**, with no hypothesis on the
simplicial semi-representable object over `X`. -/
theorem hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver :
    (homotopyAbelianTotalPushforwardOver J X K).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (TotalAbelianSheavesOver J X K) (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

attribute [local instance] hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

/-- `Ra_*`: the unbounded derived direct image along the augmentation. -/
abbrev derivedAbelianTotalPushforwardOver :
    DerivedCategory (TotalAbelianSheavesOver J X K) ⥤
      DerivedCategory (AbelianSheavesOver J X) :=
  (homotopyAbelianTotalPushforwardOver J X K).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TotalAbelianSheavesOver J X K) (ComplexShape.up ℤ))

/-- The canonical comparison from the degreewise direct image along the augmentation to
`Ra_*`. It is invertible exactly at the complexes whose direct image needs no derivation. -/
abbrev derivedAbelianTotalPushforwardOverUnit :
    homotopyAbelianTotalPushforwardOver J X K ⟶
      DerivedCategory.Qh ⋙ derivedAbelianTotalPushforwardOver J X K :=
  (homotopyAbelianTotalPushforwardOver J X K).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (TotalAbelianSheavesOver J X K) (ComplexShape.up ℤ))

/-- `a^{-1}` on unbounded derived categories, induced degreewise because `a^{-1}` is exact. -/
abbrev derivedAbelianTotalInverseImageOver :
    DerivedCategory (AbelianSheavesOver J X) ⥤
      DerivedCategory (TotalAbelianSheavesOver J X K) :=
  (abelianTotalInverseImageOver J X K).mapDerivedCategory

/-! ### The canonical map `E ⟶ Ra_* a^{-1} E` -/

/-- The unit `F ⟶ a_* a^{-1} F` of the augmentation adjunction, applied degreewise on unbounded
homotopy categories. -/
def homotopyAugmentationUnitOver :
    𝟭 (HomotopyCategory (AbelianSheavesOver J X) (ComplexShape.up ℤ)) ⟶
      (abelianTotalInverseImageOver J X K).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (abelianTotalPushforwardOver J X K).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (show (𝟭 (AbelianSheavesOver J X)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory (AbelianSheavesOver J X) (ComplexShape.up ℤ)) from
    CategoryTheory.Quotient.natIsoLift _
      (Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso (AbelianSheavesOver J X) (ComplexShape.up ℤ))
        (HomotopyCategory.quotient (AbelianSheavesOver J X) (ComplexShape.up ℤ)))).inv ≫
  NatTrans.mapHomotopyCategory (abelianTotalAdjunctionOver J X K).unit (ComplexShape.up ℤ) ≫
  (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (abelianTotalInverseImageOver J X K ⋙ abelianTotalPushforwardOver J X K))
    (ComplexShape.up ℤ)).inv

/-- The canonical map `E ⟶ Ra_* a^{-1} E` read on unbounded homotopy categories: the degreewise
augmentation unit of a complex, followed by the comparison of `a_*` with `Ra_*` at its inverse
image. -/
def derivedAugmentationUnitOverQh :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (AbelianSheavesOver J X)) ⟶
      DerivedCategory.Qh ⋙ (derivedAbelianTotalInverseImageOver J X K ⋙
        derivedAbelianTotalPushforwardOver J X K) :=
  (DerivedCategory.Qh (C := AbelianSheavesOver J X)).rightUnitor.hom ≫
    (DerivedCategory.Qh (C := AbelianSheavesOver J X)).leftUnitor.inv ≫
    Functor.whiskerRight (homotopyAugmentationUnitOver J X K) DerivedCategory.Qh ≫
    (Functor.associator
      ((abelianTotalInverseImageOver J X K).mapHomotopyCategory (ComplexShape.up ℤ))
      ((abelianTotalPushforwardOver J X K).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((abelianTotalInverseImageOver J X K).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedAbelianTotalPushforwardOverUnit J X K) ≫
    (Functor.associator
      ((abelianTotalInverseImageOver J X K).mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.Qh (C := TotalAbelianSheavesOver J X K))
      (derivedAbelianTotalPushforwardOver J X K)).inv ≫
    Functor.whiskerRight (abelianTotalInverseImageOver J X K).mapDerivedCategoryFactorsh.inv
      (derivedAbelianTotalPushforwardOver J X K) ≫
    (Functor.associator (DerivedCategory.Qh (C := AbelianSheavesOver J X))
      (derivedAbelianTotalInverseImageOver J X K)
      (derivedAbelianTotalPushforwardOver J X K)).hom

/-- **The canonical map `E ⟶ Ra_* a^{-1} E`** on the unbounded derived category of abelian
sheaves on `C/X`, for the augmentation of the total site of a simplicial semi-representable
object over `X`.

It is obtained from `derivedAugmentationUnitOverQh` through the universal property of the
localization `Qh`, so it is the map of the augmentation adjunction and not a chosen one. -/
def derivedAugmentationUnitOver :
    𝟭 (DerivedCategory (AbelianSheavesOver J X)) ⟶
      derivedAbelianTotalInverseImageOver J X K ⋙
        derivedAbelianTotalPushforwardOver J X K :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheavesOver J X) (ComplexShape.up ℤ))
    (DerivedCategory (AbelianSheavesOver J X))).preimage
      (derivedAugmentationUnitOverQh J X K)

/-- The canonical map `E ⟶ Ra_* a^{-1} E`, restricted along the localization `Qh`, is the
composite it was descended from. This is what pins the canonical map down. -/
theorem whiskerLeft_derivedAugmentationUnitOver :
    Functor.whiskerLeft DerivedCategory.Qh (derivedAugmentationUnitOver J X K) =
      derivedAugmentationUnitOverQh J X K :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheavesOver J X) (ComplexShape.up ℤ))
    (DerivedCategory (AbelianSheavesOver J X))).map_preimage _

/-- The canonical map `E ⟶ Ra_* a^{-1} E` is invertible exactly when its restriction along the
localization `Qh` is, so its invertibility may be tested on complexes. -/
theorem isIso_derivedAugmentationUnitOver_iff :
    IsIso (derivedAugmentationUnitOver J X K) ↔
      IsIso (derivedAugmentationUnitOverQh J X K) := by
  have hff := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Qh (C := AbelianSheavesOver J X))
    (HomotopyCategory.quasiIso (AbelianSheavesOver J X) (ComplexShape.up ℤ))
    (DerivedCategory (AbelianSheavesOver J X))
  constructor
  · intro h
    rw [← whiskerLeft_derivedAugmentationUnitOver]
    change IsIso (((Functor.whiskeringLeft _ _ _).obj
      (DerivedCategory.Qh (C := AbelianSheavesOver J X))).map
        (derivedAugmentationUnitOver J X K))
    infer_instance
  · intro h
    have : IsIso (((Functor.whiskeringLeft _ _ _).obj
        (DerivedCategory.Qh (C := AbelianSheavesOver J X))).map
          (derivedAugmentationUnitOver J X K)) := by
      change IsIso (Functor.whiskerLeft DerivedCategory.Qh
        (derivedAugmentationUnitOver J X K))
      rw [whiskerLeft_derivedAugmentationUnitOver]
      exact h
    exact hff.isIso_of_isIso_map (derivedAugmentationUnitOver J X K)

/-- At a complex `M` the canonical map is the localization of the ordinary augmentation unit of
`M`, followed by the comparison of `a_*` with `Ra_*` at `a^{-1}M`, followed by the isomorphism
expressing that `a^{-1}` on derived categories is induced degreewise. -/
theorem derivedAugmentationUnitOverQh_app
    (M : HomotopyCategory (AbelianSheavesOver J X) (ComplexShape.up ℤ)) :
    (derivedAugmentationUnitOverQh J X K).app M =
      DerivedCategory.Qh.map ((homotopyAugmentationUnitOver J X K).app M) ≫
        (derivedAbelianTotalPushforwardOverUnit J X K).app
          (((abelianTotalInverseImageOver J X K).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) ≫
        (derivedAbelianTotalPushforwardOver J X K).map
          ((abelianTotalInverseImageOver J X K).mapDerivedCategoryFactorsh.inv.app M) := by
  simp [derivedAugmentationUnitOverQh]

/-- The canonical map is invertible at a complex `M` as soon as the ordinary augmentation unit
of `M` is invertible and the direct image of `a^{-1}M` needs no derivation. -/
theorem isIso_derivedAugmentationUnitOverQh_app
    (M : HomotopyCategory (AbelianSheavesOver J X) (ComplexShape.up ℤ))
    (hunit : IsIso ((homotopyAugmentationUnitOver J X K).app M))
    (hacyclic : IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
      (((abelianTotalInverseImageOver J X K).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj M))) :
    IsIso ((derivedAugmentationUnitOverQh J X K).app M) := by
  rw [derivedAugmentationUnitOverQh_app]
  infer_instance

/-- **Stacks Project, Tag 0D8L**, granted its two inputs. For a simplicial semi-representable
object `K` over an object `X` of a site with fibre products, the canonical map
`E ⟶ Ra_* a^{-1} E` is an isomorphism for every `E` of `D(C/X)` — as soon as, at every complex
of abelian sheaves on `C/X`, the ordinary augmentation unit is invertible and the direct image
of its inverse image needs no derivation.

These are the two steps of the source's argument for cohomological descent, and this reduces
that argument to them. Neither is discharged in this library, so both are carried as
hypotheses and the invertibility is not proved unconditionally. -/
@[stacks 0D8L "granted two inputs this library does not have:
the degree-zero identification M = a_*a⁻¹M, which is the unproved clause of Tag 0D8K,
and the vanishing of R^p a_* a⁻¹ in positive degrees;
the isomorphism is not proved unconditionally"]
theorem isIso_derivedAugmentationUnitOver_app
    (hunit : ∀ M, IsIso ((homotopyAugmentationUnitOver J X K).app M))
    (hacyclic : ∀ M, IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
      (((abelianTotalInverseImageOver J X K).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj M)))
    (E : DerivedCategory (AbelianSheavesOver J X)) :
    IsIso ((derivedAugmentationUnitOver J X K).app E) := by
  have h : IsIso (derivedAugmentationUnitOverQh J X K) :=
    (NatTrans.isIso_iff_isIso_app _).mpr fun M =>
      isIso_derivedAugmentationUnitOverQh_app J X K M (hunit M) (hacyclic M)
  have := (isIso_derivedAugmentationUnitOver_iff J X K).mpr h
  infer_instance

end CategoryTheory.SimplicialSemiRepresentable

end
