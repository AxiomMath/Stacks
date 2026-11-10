module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.ResolutionPointCriterionPolynomialSite
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08QK at the site `C_{B/A}` itself: the values of `Lπ_!` on `𝒪`, on `B̲` and on `i^*Ω_{𝒪/A}`

Let `A → B` be a ring map and let `π`, `𝒪`, `B̲` be as in [Stacks, Tag 08PR]. [Stacks, Tag 08QK]
asserts, in `D(Ab)`,

```
Lπ_!(𝒪) = Lπ_!(B̲) = B      and      L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A}).
```

This file proves the whole first display and the first equality of the second, **at
`CommAlgCat.polynomialSite` itself** -- the site of Tag 08PR, not a restriction of it.

## Main results

* `CommAlgCat.polynomialSiteDerivedLowerShriekConstantIso`: **`Lπ_!(B̲) = B`** in `D(Ab)`.
* `CommAlgCat.polynomialSiteDerivedLowerShriekStructureConstantIso`: **`Lπ_!(𝒪) = Lπ_!(B̲)`** in
  `D(Ab)`, as the isomorphism induced by the augmentation `𝒪 ⟶ B̲`.
* `CommAlgCat.polynomialSiteDerivedLowerShriekStructureIso`: **`Lπ_!(𝒪) = B`** in `D(Ab)`, the
  composite of the two.
* `CommAlgCat.polynomialSiteDerivedLowerShriekCotangentIso`:
  **`L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`** in `D(Ab)`.

## Scope

The last equality of the tag, `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = Lπ_!(Ω_{𝒪/A})`, is not proved in this
file. It is `CommAlgCat.polynomialSiteDerivedLowerShriekDifferentialsBaseChangeIso` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentialsBaseChangeLargeSite.lean`, at `C_{B/A}`
itself and under no hypothesis on `A → B`.

It is **not** proved there along the source's route, which is [Stacks, Tag 08QJ] at
`ℱ = Ω_{𝒪/A}`: the dévissage of [Stacks, Tag 08RX] behind that tag is proved only for a site
that is a `SmallCategory` with its coefficients in `RingCat.{u}` --
`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single` and every link of its chain,
down through `Stacks.ChaoticSite.changeOfRingsAdjunction`,
`Stacks.ChaoticSite.derivedColimitTensorComparison` and
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero`. Removing that restriction is a
change of coefficients at the module level, which
`Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso` -- an equivalence for *abelian*
coefficients -- does not by itself supply. What is used instead is the Δ-instance of Tag 08RX,
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app`, which mentions no site and whose
universe is free, so that it applies at `u + 1` directly. The small-model declaration that states
the equality at the footnote-restricted site keeps no `@[stacks 08QK]`.

## Implementation notes

**Which site, and why the five existing registrations are not this.** The
`CommAlgCat.derivedLowerShriekConstantIso` and its three companions in
`StacksFrontier/Cotangent/PolynomialAlgebraSitePointValues.lean` are the same four identities
read at
`CommAlgCat.smallBoundedPolynomialSite`, the small model of the *footnote-restricted* site: the
footnote to the source's section cuts `C_{B/A}` down to the full subcategory of the augmentations
whose set of variables has cardinality at most a fixed bound. Passing to a full subcategory changes
both `Ab(-)` and `Lπ_!`, so neither reading implies the other, and the restricted statement is a
special case of the tag rather than the tag.

**The coefficient universe.** `Ab(C_{B/A})` is read at `AddCommGrpCat.{u + 1}`: the objects of the
site live in `Type (u + 1)` and its morphisms in `Type u`, so `u + 1` is the smallest universe in
which the index category of a presheaf has colimits of abelian groups. This is already the
universe at which Tag 08PR's own `𝒪` and `B̲` are formed -- `CommAlgCat.polynomialStructurePresheaf`
takes its sections in `CommRingCat.{u + 1}` through `CommAlgCat.uliftFunctor`, and
`CommAlgCat.polynomialConstantPresheaf` is constant at `ULift.{u + 1} B` -- so `B` itself appears
below as the abelian group `ULift.{u + 1} B`, exactly as the site's own ringed point
`CommAlgCat.polynomialRingedPoint` reads it.

**What had to be proved for this to be stated at all.** Three prerequisites, all of them in place
only because the restriction to a small site was removed from the machinery:

* `CommAlgCat.isInitial_polynomialBaseAugmentation` -- the augmentation `A → B`, with `A` read as
  the polynomial algebra on no variables, is an initial object of the *unrestricted* category of
  polynomial augmentations, hence a terminal object of the site. The lemma
  `CommAlgCat.isTerminal_smallPolynomialBaseObj` is the same object in the small model, and
  `CommAlgCat.polynomialIdentityObj_isTerminal` is a different object altogether, available only
  when `B` is itself a polynomial algebra.
* `Stacks.ChaoticSite.derivedConstCompColimitIso'` -- [Stacks, Tag 08Q7] in its colimit
  presentation, whose `[SmallCategory C]` hypothesis is now `[Category.{v} C]`: everything its
  proof consumes was already size-general.
* `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large` -- the
  criterion of [Stacks, Tag 08Q9] on a single morphism with no smallness hypothesis.

**Why the resolution comparison is an equality here and not an isomorphism.** In the small model
the objects of the site are only *isomorphic* to the terms of a resolution, so
`CommAlgCat.smallResolutionStructureRingIso` has to transport along a comparison. At `C_{B/A}`
itself the terms of the resolution *are* objects of the site, and
`CommAlgCat.polynomialAugmentationRing_comp_resolution` is an equality of natural
transformations.

## References

* [Stacks Project, Tag 08QK](https://stacks.math.columbia.edu/tag/08QK)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08Q7](https://stacks.math.columbia.edu/tag/08Q7)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

/-! ### The base algebra as a terminal object of `C_{B/A}` -/

section Base

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- The augmentation `A → B`, as an object of the unrestricted category of polynomial
augmentations: `A` itself, which is the polynomial algebra over `A` on no variables, augmented by
the structure map of `B`. -/
def polynomialBaseAugmentation : PolynomialAugmentation A B where
  obj := Over.mk (CommAlgCat.ofHom (MvPolynomial.aeval (R := A)
    (isEmptyElim : PEmpty.{u + 1} → (B : Type u))))
  property := ⟨PEmpty.{u + 1}, ⟨AlgEquiv.refl⟩⟩

/-- The structure map of an augmentation `α : P → B`, read as a morphism out of the augmentation
`A → B`. -/
def polynomialBaseHom (X : PolynomialAugmentation A B) :
    polynomialBaseAugmentation A B ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom (MvPolynomial.aeval (R := A)
      (isEmptyElim : PEmpty.{u + 1} → (X.obj.left : Type u))))
    (CommAlgCat.hom_ext (MvPolynomial.algHom_ext fun i => isEmptyElim i)))

/-- **The augmentation `A → B` is initial among polynomial `A`-algebras augmented to `B`**: an
augmentation `α : P → B` receives exactly one map from it, the structure map of `P`, because `A`
is an initial object of `CommAlgCat A`.

This is the unrestricted counterpart of `CommAlgCat.isInitial_boundedPolynomialBaseAugmentation`,
and it is what makes the site of [Stacks, Tag 08PR] admit a terminal object with no hypothesis on
`B`. -/
def isInitial_polynomialBaseAugmentation : IsInitial (polynomialBaseAugmentation A B) :=
  IsInitial.ofUniqueHom (polynomialBaseHom A B) fun _ _ =>
    ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <| CommAlgCat.hom_ext <|
      MvPolynomial.algHom_ext fun i => isEmptyElim i

/-- The augmentation `A → B`, read as an object of the site `C_{B/A}` of [Stacks, Tag 08PR]. -/
def polynomialBaseObj : polynomialSite A B := op (polynomialBaseAugmentation A B)

/-- **The augmentation `A → B` is a terminal object of the site `C_{B/A}`**, the site being the
opposite of the category of polynomial augmentations. -/
def isTerminal_polynomialBaseObj : IsTerminal (polynomialBaseObj A B) :=
  terminalOpOfInitial (isInitial_polynomialBaseAugmentation A B)

/-- The site `C_{B/A}` of [Stacks, Tag 08PR] has a terminal object. -/
instance hasTerminal_polynomialSite : HasTerminal (polynomialSite A B) :=
  (isTerminal_polynomialBaseObj A B).hasTerminal

end Base

/-! ### `Lπ_!` on `Ab(C_{B/A})` -/

section Shriek

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- `Lπ_! : D(Ab(C_{B/A})) ⥤ D(Ab)` at the site `C_{B/A}` of [Stacks, Tag 08PR] itself, the total
left derived functor of the colimit over the index category -- which is the `π_!` of
[Stacks, Tag 08PF] on a chaotic site. The coefficients are at `AddCommGrpCat.{u + 1}`, the
universe of the site's own `𝒪` and `B̲`. -/
abbrev polynomialSiteAbelianDerivedLowerShriek :
    DerivedCategory ((polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  totalDerivedColimit' (polynomialSite A B) AddCommGrpCat.{u + 1}

/-- `Lπ_!(ℱ)` for an abelian presheaf `ℱ` on `C_{B/A}` placed in cohomological degree zero. -/
abbrev polynomialSiteDerivedLowerShriekSingle
    (F : (polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  (polynomialSiteAbelianDerivedLowerShriek A B).obj (DerivedCategory.Q.obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- The forgetful functor from commutative rings to abelian groups, which reads a presheaf of
rings on `C_{B/A}` as an abelian presheaf. -/
abbrev commRingToAbelian : CommRingCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙ forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}

/-- **`𝒪` read on its underlying abelian presheaf.** This is the structure sheaf of
[Stacks, Tag 08PR], `CommAlgCat.polynomialStructurePresheaf`, whose sections at `(P, α)` are `P`,
read on abelian groups so that `Lπ_!` of [Stacks, Tag 08Q6] can be applied to it. -/
abbrev polynomialSiteAbelianStructurePresheaf :
    (polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  polynomialStructurePresheaf A B ⋙ commRingToAbelian

/-- **`B̲` read on its underlying abelian presheaf**, the constant sheaf of [Stacks, Tag 08PR]. -/
abbrev polynomialSiteAbelianConstantPresheaf :
    (polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  polynomialConstantPresheaf A B ⋙ commRingToAbelian

/-- **The augmentation `𝒪 ⟶ B̲` read on the underlying abelian presheaves.** -/
abbrev polynomialSiteAbelianAugmentation :
    polynomialSiteAbelianStructurePresheaf A B ⟶ polynomialSiteAbelianConstantPresheaf A B :=
  Functor.whiskerRight (polynomialAugmentationPresheaf A B) commRingToAbelian

/-- `B`, as an abelian group in the universe of the site's sections: the additive group of
`ULift.{u + 1} B`, which is the ring of the site's own ringed point
`CommAlgCat.polynomialRingedPoint`. -/
abbrev polynomialSiteAbelianOfBase : AddCommGrpCat.{u + 1} :=
  commRingToAbelian.obj (CommRingCat.of (ULift.{u + 1} (B : Type u)))

/-- `B`, as an object of `D(Ab)`. -/
abbrev polynomialSiteBaseInDerived : DerivedCategory AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q.obj ((HomologicalComplex.single AddCommGrpCat.{u + 1}
    (ComplexShape.up ℤ) 0).obj (polynomialSiteAbelianOfBase A B))

/-- The abelian presheaf underlying `B̲` is the constant presheaf with value `B`. -/
def polynomialSiteConstantPresheafAbelianIso :
    polynomialSiteAbelianConstantPresheaf A B ≅
      (Functor.const (polynomialSite A B)ᵒᵖ).obj (polynomialSiteAbelianOfBase A B) :=
  Functor.constComp _ _ _

/-- The constant diagram on `M[0]`, read in the derived category, is `(π^{-1}M)[0]`. -/
def polynomialSiteDerivedConstSingleIso (M : AddCommGrpCat.{u + 1}) :
    (Functor.const (polynomialSite A B)ᵒᵖ :
          AddCommGrpCat.{u + 1} ⥤ _).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) 0).obj M)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((Functor.const (polynomialSite A B)ᵒᵖ).obj M)) :=
  (Functor.const (polynomialSite A B)ᵒᵖ :
      AddCommGrpCat.{u + 1} ⥤ _).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Functor.const (polynomialSite A B)ᵒᵖ) (ComplexShape.up ℤ) 0).app M)

/-- **`Lπ_!(B̲) = B` in `D(Ab)` at the site `C_{B/A}` itself**, the second identification of
[Stacks, Tag 08QK]. Here `B̲` is the constant sheaf of rings with value `B` of
[Stacks, Tag 08PR] read on its underlying abelian sheaf, `π` is the point morphism of the site
`C_{B/A}` of that tag -- not of a restriction of it -- and `Lπ_!` is the total left derived
functor of the colimit over the index category, which is the `π_!` of [Stacks, Tag 08PF].

The proof is the source's: the polynomial algebra on no variables, augmented by `A → B`, is a
terminal object of the site (`CommAlgCat.isTerminal_polynomialBaseObj`), so `π^{-1}` is the
constant diagram and has an exact right adjoint, and [Stacks, Tag 08Q7] in the form
`Stacks.ChaoticSite.derivedConstCompColimitIso'` gives `Lπ_! ∘ π^{-1} = id`. -/
@[stacks 08QK "Lπ_!(B̲) = B in D(Ab), for the point morphism of the site C_{B/A} of Tag 08PR \
  itself -- not of the footnote-restricted site nor of a small model of it -- with Lπ_! the total \
  left derived functor of the colimit over the index category, which is the π_! of Tag 08PF, and \
  with B read as the abelian group ULift.{u+1} B exactly as the site's own ringed point \
  CommAlgCat.polynomialRingedPoint reads it"]
def polynomialSiteDerivedLowerShriekConstantIso :
    polynomialSiteDerivedLowerShriekSingle A B (polynomialSiteAbelianConstantPresheaf A B) ≅
      polynomialSiteBaseInDerived A B :=
  (polynomialSiteAbelianDerivedLowerShriek A B).mapIso (DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (polynomialSiteConstantPresheafAbelianIso A B))) ≪≫
    (polynomialSiteAbelianDerivedLowerShriek A B).mapIso
      (polynomialSiteDerivedConstSingleIso A B (polynomialSiteAbelianOfBase A B)).symm ≪≫
    (Stacks.ChaoticSite.derivedConstCompColimitIso' (polynomialSite A B)
      AddCommGrpCat.{u + 1} (Or.inr inferInstance)).app (polynomialSiteBaseInDerived A B)

/-! ### The universe lift that relates `𝒪` to the `Type u` presheaf of rings -/

/-- The forgetful functor from rings to abelian groups followed by the universe lift of the
sections: the route along which the `Type u` presheaf of rings
`CommAlgCat.polynomialStructurePresheafRing` becomes an abelian presheaf at the coefficient
universe of the site. -/
abbrev ringToAbelianLift : RingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- **`𝒪` read on abelian groups is the universe lift of the `Type u` presheaf of rings.** Both
sides send the object `(P, α)` to the additive group of `ULift.{u + 1} P`: the left side because
`CommAlgCat.polynomialStructurePresheaf` is built through `CommAlgCat.uliftFunctor`, the right
side because `CommAlgCat.polynomialStructurePresheafRing` has its sections in `Type u` and they
are lifted afterwards.

This is the only piece of universe bookkeeping in the file. It is what lets the evaluation of the
augmentation on a resolution be read off the *equality*
`CommAlgCat.polynomialAugmentationRing_comp_resolution`, which holds at `C_{B/A}` itself. -/
def polynomialSiteAbelianStructurePresheafLiftIso :
    polynomialSiteAbelianStructurePresheaf A B ≅
      polynomialStructurePresheafRing A B ⋙ ringToAbelianLift :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **`B̲` read on abelian groups is the universe lift of the constant `Type u` presheaf of
rings.** -/
def polynomialSiteAbelianConstantPresheafLiftIso :
    polynomialSiteAbelianConstantPresheaf A B ≅
      (Functor.const (polynomialSite A B)ᵒᵖ).obj (ringOfBase A B) ⋙ ringToAbelianLift :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The augmentation `𝒪 ⟶ B̲` on abelian groups is the universe lift of the augmentation of
`Type u` presheaves of rings**, under the two identifications above. -/
lemma polynomialSiteAbelianAugmentation_liftIso :
    polynomialSiteAbelianAugmentation A B ≫
        (polynomialSiteAbelianConstantPresheafLiftIso A B).hom =
      (polynomialSiteAbelianStructurePresheafLiftIso A B).hom ≫
        Functor.whiskerRight (polynomialAugmentationRing A B) ringToAbelianLift :=
  NatTrans.ext (funext fun _ => rfl)

/-! ### The standard resolution as a point resolution of `C_{B/A}` -/

/-- The standard resolution of `B` over `A`, read as a cosimplicial object of the site `C_{B/A}`
of [Stacks, Tag 08PR] itself. Unlike `CommAlgCat.standardResolutionSmallCosimplicialObject`, whose
objects are only isomorphic to the terms of the resolution, the objects here *are* those terms. -/
abbrev standardResolutionPolynomialSiteCosimplicialObject :
    CosimplicialObject (polynomialSite A B) :=
  resolutionCosimplicialObject (standardResolution.{u, u} A B).hom
    fun n => (standardResolution_isPolynomialAlgebraBelow A B n).isPolynomialAlgebra

/-- **The standard resolution is a point resolution of the site `C_{B/A}` itself**, which is
[Stacks, Tag 08PS] at that site. -/
theorem isPointResolution_standardResolutionPolynomialSiteCosimplicialObject :
    Stacks.ChaoticSite.IsPointResolution
      (standardResolutionPolynomialSiteCosimplicialObject A B) :=
  isPointResolution_resolutionCosimplicialObject (standardResolution.{u, u} A B).hom _
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration

/-- The route from `A`-algebras to abelian groups along which `𝒪` is built: through commutative
rings and rings, at `Type u`. -/
abbrev algebraToAbelian : CommAlgCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u}

/-- **The augmentation of the standard resolution is a quasi-isomorphism of associated
complexes.** This is [Stacks, Tag 08QI]: the standard resolution is a resolution, and for a
degreewise surjective augmentation of degreewise polynomial simplicial algebras that is equivalent
to the induced map of alternating face map complexes being a quasi-isomorphism.

The two routes from `CommAlgCat.{u} A` to `AddCommGrpCat.{u}` -- through `CommRingCat` and
`RingCat`, which is how `𝒪` is built, and through `AlgCat A` and `ModuleCat A`, which is how
Tag 08QI is stated -- are the same functor on the nose, so no comparison enters. -/
theorem quasiIso_alternatingFaceMapComplex_standardResolution :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight (standardResolution.{u, u} A B).hom (algebraToAbelian A))) := by
  have hε : ∀ n : SimplexCategoryᵒᵖ,
      Function.Surjective (((standardResolution.{u, u} A B).hom.app n).hom) := fun n => by
    have hn : n = op (SimplexCategory.mk n.unop.len) := by rw [SimplexCategory.mk_len]
    rw [hn]
    exact surjective_standardResolution_augmentation A B n.unop.len
  exact ((isResolution_quasiIso_homotopyEquivalence_tfae A B _
    (standardResolution.{u, u} A B).hom
    (fun n => (standardResolution_isPolynomialAlgebraBelow A B n).isPolynomialAlgebra)
    hε).out 1 2).mp (standardResolution_isResolution.{u, u} A B)

/-- **The same quasi-isomorphism after the universe lift of the sections.**
`AddCommGrpCat.uliftFunctor` is additive and preserves homology, so it carries a
quasi-isomorphism to a quasi-isomorphism, and
`AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso` moves it past the
alternating face map complex. -/
theorem quasiIso_alternatingFaceMapComplex_standardResolutionLift :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight
        (Functor.whiskerRight (standardResolution.{u, u} A B).hom (algebraToAbelian A))
        AddCommGrpCat.uliftFunctor.{u + 1, u})) := by
  have := quasiIso_alternatingFaceMapComplex_standardResolution A B
  have e := AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (e.app _).symm (e.app _).symm
    (e.inv.naturality
      (Functor.whiskerRight (standardResolution.{u, u} A B).hom (algebraToAbelian A))).symm)).2
    inferInstance

/-- **The augmentation `𝒪 ⟶ B̲` becomes a quasi-isomorphism on the extended Moore complex of its
evaluation on the standard resolution, at the site `C_{B/A}` itself.**

This is the hypothesis in which the criterion of [Stacks, Tag 08Q9] asks for
`Lπ_!(𝒪) = Lπ_!(B̲)`. Nothing about resolutions is reproved: the evaluation of `𝒪 ⟶ B̲` on the
cosimplicial object of a resolution is the augmentation `ε` of that resolution, by the *equality*
`CommAlgCat.polynomialAugmentationRing_comp_resolution`, and that `ε` induces a
quasi-isomorphism is [Stacks, Tag 08QI]. The universe lift of the sections is the only extra
step, and it is `CommAlgCat.polynomialSiteAbelianAugmentation_liftIso` together with the
exactness of `AddCommGrpCat.uliftFunctor`. -/
theorem quasiIso_mooreCochain_polynomialSiteAbelianAugmentation :
    QuasiIso ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
      (standardResolutionPolynomialSiteCosimplicialObject A B)
      AddCommGrpCat.{u + 1}).map (polynomialSiteAbelianAugmentation A B)) := by
  set U := standardResolutionPolynomialSiteCosimplicialObject A B
  set M := Stacks.ChaoticSite.GeneralValued.mooreCochainComplex' U AddCommGrpCat.{u + 1}
  have harr : Arrow.mk (M.map (polynomialSiteAbelianAugmentation A B)) ≅
      Arrow.mk (M.map (Functor.whiskerRight (polynomialAugmentationRing A B)
        ringToAbelianLift)) :=
    Arrow.isoMk (M.mapIso (polynomialSiteAbelianStructurePresheafLiftIso A B))
      (M.mapIso (polynomialSiteAbelianConstantPresheafLiftIso A B))
      (by
        simp only [Functor.mapIso_hom, Arrow.mk_hom, ← Functor.map_comp]
        exact congrArg M.map (polynomialSiteAbelianAugmentation_liftIso A B).symm)
  refine (quasiIso_iff_of_arrow_mk_iso _ _ harr).2 ?_
  have hcomp : QuasiIso ((Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex'
      AddCommGrpCat.{u + 1} U).map
        (Functor.whiskerRight (polynomialAugmentationRing A B) ringToAbelianLift)) := by
    have key : (Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex'
          AddCommGrpCat.{u + 1} U).map
            (Functor.whiskerRight (polynomialAugmentationRing A B) ringToAbelianLift) =
        (alternatingFaceMapComplex AddCommGrpCat.{u + 1}).map
          (Functor.whiskerRight
            (Functor.whiskerRight (standardResolution.{u, u} A B).hom (algebraToAbelian A))
            AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
      change (alternatingFaceMapComplex AddCommGrpCat.{u + 1}).map
          (Functor.whiskerRight
            (Functor.whiskerLeft U.op (polynomialAugmentationRing A B)) ringToAbelianLift) = _
      rw [polynomialAugmentationRing_comp_resolution A B (standardResolution.{u, u} A B).hom
        (fun n => (standardResolution_isPolynomialAlgebraBelow A B n).isPolynomialAlgebra)]
      rfl
    rw [key]
    exact quasiIso_alternatingFaceMapComplex_standardResolutionLift A B
  exact (HomologicalComplex.quasiIso_extendMap_iff _
    (ComplexShape.embeddingUpIntLE (0 : ℤ))).2 hcomp

/-- **`Lπ_!(𝒪) = Lπ_!(B̲)` in `D(Ab)` at the site `C_{B/A}` itself**, the first identification of
[Stacks, Tag 08QK], as the isomorphism **induced by the augmentation `𝒪 ⟶ B̲`** of
[Stacks, Tag 08PR].

The two inputs are the criterion of [Stacks, Tag 08Q9] with no smallness hypothesis on the site,
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large`, and the
quasi-isomorphism of Moore complexes
`CommAlgCat.quasiIso_mooreCochain_polynomialSiteAbelianAugmentation`, whose own input is
[Stacks, Tag 08QI]. -/
@[stacks 08QK "Lπ_!(𝒪) = Lπ_!(B̲) in D(Ab), as the isomorphism induced by the augmentation \
  𝒪 ⟶ B̲ of Tag 08PR, for the point morphism of the site C_{B/A} of Tag 08PR itself -- not of \
  the footnote-restricted site nor of a small model of it"]
def polynomialSiteDerivedLowerShriekStructureConstantIso :
    polynomialSiteDerivedLowerShriekSingle A B (polynomialSiteAbelianStructurePresheaf A B) ≅
      polynomialSiteDerivedLowerShriekSingle A B (polynomialSiteAbelianConstantPresheaf A B) :=
  haveI : IsIso ((polynomialSiteAbelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (polynomialSiteAbelianAugmentation A B)))) :=
    (Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff_of_large
        (standardResolutionPolynomialSiteCosimplicialObject A B)
        (isPointResolution_standardResolutionPolynomialSiteCosimplicialObject A B) _).2
      (quasiIso_mooreCochain_polynomialSiteAbelianAugmentation A B)
  asIso ((polynomialSiteAbelianDerivedLowerShriek A B).map (DerivedCategory.Q.map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (polynomialSiteAbelianAugmentation A B))))

/-- **`Lπ_!(𝒪) = B` in `D(Ab)` at the site `C_{B/A}` itself**, the composite of the two
identifications `Lπ_!(𝒪) = Lπ_!(B̲)` and `Lπ_!(B̲) = B` of [Stacks, Tag 08QK]. -/
@[stacks 08QK "Lπ_!(𝒪) = B in D(Ab), for the point morphism of the site C_{B/A} of Tag 08PR \
  itself -- not of the footnote-restricted site nor of a small model of it"]
def polynomialSiteDerivedLowerShriekStructureIso :
    polynomialSiteDerivedLowerShriekSingle A B (polynomialSiteAbelianStructurePresheaf A B) ≅
      polynomialSiteBaseInDerived A B :=
  polynomialSiteDerivedLowerShriekStructureConstantIso A B ≪≫
    polynomialSiteDerivedLowerShriekConstantIso A B

/-! ### `L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` at the site `C_{B/A}` -/

/-- The forgetful functor from `B`-modules to abelian groups followed by the universe lift of the
sections: the route along which a sheaf of `B`-modules with sections in `Type u` is read at the
coefficient universe of the site. -/
abbrev moduleToAbelianLift : ModuleCat.{u} (B : Type u) ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- **`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` on the site `C_{B/A}`, read as an abelian presheaf at the
coefficient universe of the site.** The underlying presheaf of `B`-modules is
`CommAlgCat.polynomialCotangentModulePresheaf`, which sends `(P, α)` to `B ⊗_{P,α} Ω[P⁄A]` --
how the source describes `i^*Ω_{𝒪/A}` in the proof of [Stacks, Tag 08PU]. The topology of
`C_{B/A}` being chaotic, no sheafification intervenes. -/
abbrev polynomialSiteAbelianCotangentPresheaf :
    (polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  polynomialCotangentModulePresheaf A B ⋙ moduleToAbelianLift A B

/-- `L_{B/A}`, the cotangent complex of [Stacks, Tag 08PN], as an object of `D(Ab)` at the
coefficient universe of the site. -/
abbrev polynomialSiteCotangentInDerived : DerivedCategory AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q.obj
    (((moduleToAbelianLift A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cotangentComplex.{u, u} A B))

/-- **The extended Moore complex of `(i^*Ω_{𝒪/A})(P_•, ε)` for the standard resolution is the
complex of `L_{B/A}`**, at the site `C_{B/A}` itself, as an isomorphism of complexes.

This is the heart of [Stacks, Tag 08PU], and at `C_{B/A}` it needs no comparison on the source:
the evaluation of `i^*Ω_{𝒪/A}` on the cosimplicial object of the standard resolution *is* the
simplicial module of base-changed differentials, by definition, where
`CommAlgCat.smallResolutionCotangentModuleIso` has to transport along an isomorphism because the
small model's objects are only isomorphic to the terms of the resolution.
`CommAlgCat.standardResolutionOverDifferentialsIso` then identifies that with the simplicial
module of [Stacks, Tag 08PN]. -/
def polynomialSiteCotangentMooreComplexIso :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
          (standardResolutionPolynomialSiteCosimplicialObject A B)
          AddCommGrpCat.{u + 1}).obj (polynomialSiteAbelianCotangentPresheaf A B) ≅
      ((moduleToAbelianLift A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, u} A B) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor AddCommGrpCat.{u + 1}).mapIso
      ((alternatingFaceMapComplex AddCommGrpCat.{u + 1}).mapIso
          (Functor.isoWhiskerRight (standardResolutionOverDifferentialsIso A B)
            (moduleToAbelianLift A B)) ≪≫
        ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
          (moduleToAbelianLift A B)).app
            (cotangentSimplicialModule.{u, u} A B).object).symm) ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso (moduleToAbelianLift A B)
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- **`L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` in `D(Ab)` at the site `C_{B/A}` itself**, the third
identification of [Stacks, Tag 08QK]. The left-hand side is the cotangent complex of
[Stacks, Tag 08PN] with its `B`-module structures forgotten, read at the coefficient universe of
the site; the right-hand side is `Lπ_!` of the abelian sheaf `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲`.

The two inputs are [Stacks, Tag 08PS] at `C_{B/A}` itself,
`CommAlgCat.polynomialSiteResolutionDerivedColimitNatIso`, which computes `Lπ_!` by the extended
Moore complex of the evaluation on the standard resolution, and
`CommAlgCat.polynomialSiteCotangentMooreComplexIso`, which is [Stacks, Tag 08PU] identifying that
Moore complex with the complex of `L_{B/A}`. -/
@[stacks 08QK "L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) in D(Ab), for the point morphism of the site \
  C_{B/A} of Tag 08PR itself -- not of the footnote-restricted site nor of a small model of it: \
  the cotangent complex of Tag 08PN, read in D(Ab) at the coefficient universe of the site, is \
  Lπ_! of the sheaf i^*Ω_{𝒪/A}"]
def polynomialSiteDerivedLowerShriekCotangentIso :
    polynomialSiteDerivedLowerShriekSingle A B (polynomialSiteAbelianCotangentPresheaf A B) ≅
      polynomialSiteCotangentInDerived A B :=
  ((polynomialSiteResolutionDerivedColimitNatIso (standardResolution.{u, u} A B).hom
          (fun n => (standardResolution_isPolynomialAlgebraBelow A B n).isPolynomialAlgebra)
          (standardResolution_isResolution.{u, u} A B).trivialKanFibration).app
        (polynomialSiteAbelianCotangentPresheaf A B)).symm ≪≫
    DerivedCategory.Q.mapIso (polynomialSiteCotangentMooreComplexIso A B)

end Shriek

end CommAlgCat

end
