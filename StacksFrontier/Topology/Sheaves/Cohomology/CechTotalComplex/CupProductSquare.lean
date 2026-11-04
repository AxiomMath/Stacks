module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductComparisonBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.SheafTensorPairing
public import StacksFrontier.Homology.Tor.DerivedTensorToTotalComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductThroughThePoint

/-!
# The two columns of the cup-product square of Tag 0FKV, in one category

Let `(S, 𝒪_S)` be a ringed space, put `A = Γ(S, 𝒪_S)`, let `𝒦^•` and `ℳ^•` be bounded below
complexes of `𝒪_S`-modules and let `𝒰 : S = ⋃ U i` be an open covering.  [Stacks, Tag 0FKV]
asserts that the six-vertex diagram

```
Tot(Č(𝒰,𝒦)) ⊗^𝐋_A Tot(Č(𝒰,ℳ)) ─────────→ RΓ(S,𝒦) ⊗^𝐋_A RΓ(S,ℳ)
            │                                        │ μ
            ↓                                        ↓
Tot(Tot(Č(𝒰,𝒦)) ⊗_A Tot(Č(𝒰,ℳ)))          RΓ(S, 𝒦 ⊗^𝐋_{𝒪_S} ℳ)
            │                                        │
            ↓                                        ↓
Tot(Č(𝒰, Tot(𝒦 ⊗_{𝒪_S} ℳ))) ─────────────→ RΓ(S, Tot(𝒦 ⊗_{𝒪_S} ℳ))
```

commutes in `D(A)`, the two horizontal arrows being the comparison of [Stacks, Tag 08BN].

This file writes the two columns of that diagram as morphisms between the same objects of
`D(A)`, which takes three identifications.

* The left column ends in `Stacks.Cech.Linear.derivedSectionsFunctor`, the bounded below right
  derived functor of sections in which Tag 08BN is stated, while `μ` lives on
  `Stacks.Cohomology.GlobalKunneth.baseSections`, the unbounded total right derived functor along
  K-injective resolutions.  `cechToBaseSections` composes the Tag 08BN comparison with the bridge
  `Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections` between the two
  models, so both columns now land in `baseSections`.
* The top left vertical is the canonical map `x ⊗^𝐋_A y ⟶ Tot(x ⊗_A y)` over the *ring* `A`.  It
  is **not** the K-flat comparison recorded by `CochainComplex.DerivedTensor.DerivedTensorProduct`
  -- that is an `Iso`, available only for a pair of K-flat complexes, and `Tot(Č(𝒰,𝒦))` over `A`
  is not K-flat for an arbitrary bounded below `𝒦^•`.  It is the
  `CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorNatTrans`, instantiated here at
  the pair of total Čech complexes.
* The bottom horizontal needs the target `Tot(𝒦^• ⊗_{𝒪_S} ℳ^•)` as a *bounded below* complex;
  `tensorPlus` supplies it.

## Main definitions

* `Stacks.Cech.CupProductSquare.cechToBaseSections`: **the comparison of [Stacks, Tag 08BN] read
  into the model of `RΓ(S, -)` the cup product is stated in.**
* `Stacks.Cech.CupProductSquare.sectionsToBaseSections`: the unit `Γ(S, -) ⟶ RΓ(S, -)` in the same
  model.
* `Stacks.Cech.CupProductSquare.tensorPlus`: the total tensor complex of two bounded below
  complexes, as a bounded below complex.
* `Stacks.Cech.CupProductSquare.cechLeftLeg` and
  `Stacks.Cech.CupProductSquare.cechRightLeg`: **the two legs of the square of Tag 0FKV**, as two
  morphisms of `D(A)` with the same source and the same target.
* `Stacks.Cech.CupProductSquare.CupProductSquareCommutes`: the assertion of Tag 0FKV, that those
  two legs are equal; it holds for every pair, by
  `Stacks.Cech.CupProductSquare.cupProductSquareCommutes`.

## Main results

* `Stacks.Cech.CupProductSquare.isStrictlyGE_mapBifunctor_sheafTensor`: the total tensor complex
  of two complexes vanishing below `a` and below `b` vanishes below `a + b`.
* `Stacks.Cech.CupProductSquare.sectionsToTotalCechDerived_comp_cechToBaseSections`: **the
  pinning.**  After the augmentation of [Stacks, Tag 07M9] the comparison is the unit
  `Γ(S, 𝒦^•) ⟶ RΓ(S, 𝒦^•)`.  This is the `sections` field of
  `Stacks.Cech.Linear.CechToDerivedSectionsSystem` carried through the model bridge, and it is
  what makes the composite independent of the covering.
* `Stacks.Cech.CupProductSquare.isIso_cechToBaseSections_app_of_isFlasque` and
  `Stacks.Cech.CupProductSquare.isIso_sectionsToBaseSections_app_of_isFlasque`: **on a bounded
  below complex of flasque modules both horizontal arrows of the square are invertible.**  This is
  the identification `Γ(S,𝒦^•) = Tot(Č^•(𝒰,𝒦^•)) = RΓ(S,𝒦^•)` that the proof of Tag 0FKV reduces
  its diagram to, delivered in `D(A)` and in the model `μ` is stated in -- which is what a
  consumer of that reduction needs and what the identification did not previously provide.
* `Stacks.Cech.CupProductSquare.sectionsToTotalCechDerived_comp_cechRightLeg`: **the right-hand
  column of Tag 0FKV's square, precomposed with the Čech augmentation in both tensor factors, is
  the right-hand column of the diagram the source displays just before Tag 0FKV** -- the one with
  `Γ(S,𝒦^•) ⊗^𝐋_A Γ(S,ℳ^•)` in the top left corner, which is Tag 0FP3 for the morphism to a
  point.  It holds for every covering and every pair, with no requirement on `μ`.

## The commutativity

The square commutes: this is `Stacks.Cech.CupProductSquare.cupProductSquareCommutes`, in
`StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareCommutes`.  Its proof
reduces to a flasque pair, cancels the Čech augmentation there, and compares with the diagram with
`Γ(S, -)` in place of `Tot(Č(𝒰, -))`, which is Tag 0FP3 for the morphism from `S` to the
one-point space with ring `A`.

The bottom horizontal arrow is used only as a map.  Invertibility of the horizontal arrows is
needed only on `𝒦^•` and on `ℳ^•`, not on `Tot(𝒦^• ⊗_{𝒪_S} ℳ^•)` (a tensor product of flasque
modules need not be flasque); accordingly `isIso_cechToBaseSections_app_of_isFlasque` is stated
for one complex at a time.

## Implementation notes

The spellings cross with no transport.  The
hand-built tensor bifunctor `Stacks.Cech.CupProduct.tensorModules A` of the Čech cup product is
Mathlib's `MonoidalCategory.curriedTensor (ModuleCat A)` by `rfl`; the derived tensor product
`CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A` over the coefficient ring
`Stacks.Cech.ModuleCupProduct.CoeffRing 𝒪_S ⊤` is `Stacks.Cohomology.GlobalKunneth.tensorBase S`
by `rfl` -- the two spellings `CoeffRing 𝒪_S ⊤` and `Γ(S, 𝒪_S)` of `A` agree on the nose, which
is `Stacks.Cech.ModuleCupProduct.sectionCommRing_toRing`; the ordinary total tensor complex that
the top left vertical lands in is the source of the Čech cup product by `rfl`; and the source of
the Tag 08BN comparison on a bounded below complex is `Q` of the cup product's total Čech complex
by `rfl`, which is `Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA_eq`.  Only the two
models of `RΓ(S, -)` need a genuine isomorphism between them.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (abSheaf)
open Stacks.Cohomology.DerivedGlobalCupProduct (canonicalOnePointComparison globalCupProduct)
open Stacks.Cohomology.DerivedSectionsModels (derivedSectionsFunctorIsoBaseSections)
open Stacks.Cohomology.GlobalKunneth (baseSections tensorBase)
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing totalCechComplexFunctorA)
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorNatTrans)
open scoped CategoryTheory.Prod

universe u

namespace CochainComplex.DerivedTensor.ToTotal

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

/-- **The canonical map `x ⊗^𝐋_R y ⟶ Tot(x ⊗_R y)` followed by a map out of the total tensor
complex**, for complexes `X`, `Y`, `Z` of `R`-modules and a cochain map
`Tot(X ⊗_R Y) ⟶ Z`.  The source of `cup` is written with `Stacks.Cech.CupProduct.tensorModules`,
the spelling of the Čech cup product of [Stacks, Tag 07MB] and of the naive cup product. -/
def canonicalDerivedToTensorComp (R : Type u) [CommRing R]
    (X Y Z : CochainComplex (ModuleCat.{u} R) ℤ)
    (cup : HomologicalComplex.mapBifunctor X Y (Stacks.Cech.CupProduct.tensorModules R) (up ℤ) ⟶
      Z) :
    (Functor.uncurry.obj (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R)).obj
        (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ⟶ DerivedCategory.Q.obj Z :=
  (canonicalDerivedToTensorNatTrans R).app (X, Y) ≫ DerivedCategory.Q.map cup

end CochainComplex.DerivedTensor.ToTotal

namespace Stacks.Cech.CupProductSquare

open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorComp)

attribute [local instance] HasDerivedCategory.standard

/-- Reassociation with the first leg rewritten, stated with every object and morphism a
variable.  It is applied below by `exact`, which is one `isDefEq` check; the same reassociation
performed by `rw` in the concrete statement is rejected, because the two spellings
`Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_S` and `structureSheafRing S` of the
structure sheaf of rings agree only at default transparency, while `rw` re-checks the goal at
`implicit`. -/
private theorem comp_comp_of_eq {C : Type*} [Category* C] {a b c d : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : a ⟶ c) (hk : f ≫ g = k) :
    f ≫ g ≫ h = k ≫ h := by
  rw [← Category.assoc, hk]

/-- A morphism followed by the component of a natural isomorphism is invertible as soon as the
morphism is.  Stated with every object a variable, for the same reason as `comp_comp_of_eq`: the
instance `IsIso` of the composite is not synthesized at the concrete spelling. -/
private theorem isIso_comp_hom_app {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) {X : C} {Z : D} (f : Z ⟶ F.obj X) (hf : IsIso f) :
    IsIso (f ≫ e.hom.app X) := by
  have := hf
  infer_instance

/-- Two legs of a bifunctor's source rewritten at once, stated with every object and morphism a
variable; applied below by `exact`, for the same reason as `comp_comp_of_eq`. -/
private theorem map_prod_comp_of_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C × D ⥤ E) {a b c : C} {a' b' c' : D} {z : E}
    (f₁ : a ⟶ b) (g₁ : b ⟶ c) (k₁ : a ⟶ c) (f₂ : a' ⟶ b') (g₂ : b' ⟶ c') (k₂ : a' ⟶ c')
    (r : F.obj (c, c') ⟶ z) (h₁ : f₁ ≫ g₁ = k₁) (h₂ : f₂ ≫ g₂ = k₂) :
    F.map (f₁ ×ₘ f₂) ≫ F.map (g₁ ×ₘ g₂) ≫ r = F.map (k₁ ×ₘ k₂) ≫ r := by
  rw [← Category.assoc, ← F.map_comp, prod_comp, h₁, h₂]

variable (S : RingedSpace.{u, u})

/-! ### The total tensor complex of two bounded below complexes -/

/-- **The total tensor complex of two complexes vanishing below `a` and below `b` vanishes below
`a + b`.**  Every summand `𝒦^p ⊗_{𝒪_S} ℳ^q` of the term in a degree `i < a + b` has `p < a` or
`q < b`, so one factor vanishes and the summand vanishes with it. -/
theorem isStrictlyGE_mapBifunctor_sheafTensor
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (a b : ℤ)
    [CochainComplex.IsStrictlyGE K a] [CochainComplex.IsStrictlyGE M b] :
    CochainComplex.IsStrictlyGE
      (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf) (up ℤ)) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  have hz : IsZero (((sheafTensor S.sheaf).obj (K.X p)).obj (M.X q)) := by
    by_cases hp : p < a
    · exact ((sheafTensor S.sheaf).map_isZero (K.isZero_of_isStrictlyGE a p hp)).obj _
    · exact ((sheafTensor S.sheaf).obj (K.X p)).map_isZero
        (M.isZero_of_isStrictlyGE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- **The total tensor complex `Tot(𝒦^• ⊗_{𝒪_S} ℳ^•)` of two bounded below complexes, as a
bounded below complex.**  This is the bottom right vertex of the diagram of [Stacks, Tag 0FKV];
the comparison of [Stacks, Tag 08BN] into it exists only for a bounded below complex. -/
def tensorPlus (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) :=
  ⟨HomologicalComplex.mapBifunctor K.1 M.1 (sheafTensor S.sheaf) (up ℤ), by
    obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K.1).mp K.2
    obtain ⟨b, hb⟩ := (CochainComplex.plus_iff _ M.1).mp M.2
    have := ha
    have := hb
    exact ⟨a + b, isStrictlyGE_mapBifunctor_sheafTensor S K.1 M.1 a b⟩⟩

/-- The underlying cochain complex of `tensorPlus S K M` is the total tensor complex
`Tot(K ⊗_{𝒪_S} M)` of the underlying complexes of `K` and `M`. -/
@[simp]
theorem tensorPlus_obj
    (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    (tensorPlus S K M).1 =
      HomologicalComplex.mapBifunctor K.1 M.1 (sheafTensor S.sheaf) (up ℤ) :=
  rfl

/-! ### The comparison of Tag 08BN in the model the cup product is stated in -/

variable {I : Type u} (Ui : I → Opens S.carrier) (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)

/-- **The comparison of [Stacks, Tag 08BN], read into the unbounded model of `RΓ(S, -)`.**  The
module-valued comparison `Tot(Č^•(𝒰, 𝒦^•)) ⟶ R⁺Γ(S, 𝒦^•)` of
`Stacks.Cech.Linear.cechToDerivedSections`, followed by the bridge
`Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections` identifying
`R⁺Γ(S, -)` with `Stacks.Cohomology.GlobalKunneth.baseSections`, the derived global sections the
global cup product of Cohomology, Section 0FKU is stated at.  This is the bottom horizontal arrow
of the diagram of [Stacks, Tag 0FKV], and -- read at the two coefficient complexes -- the top
horizontal one. -/
def cechToBaseSections :
    Stacks.Cech.Linear.totalCechDerivedFunctor S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU ⟶
      CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ baseSections S :=
  Stacks.Cech.Linear.totalCechToDerivedSections S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤
      Ui hU ≫
    (derivedSectionsFunctorIsoBaseSections S).hom

/-- The comparison at one complex, with the two factors displayed.  The identification of the
`.app` of a composite with the composite of the `.app`s is paid once, here, and every statement
below rewrites with this rather than unfolding the definition again. -/
theorem cechToBaseSections_app
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    (cechToBaseSections S Ui hU).app K =
      (Stacks.Cech.Linear.totalCechToDerivedSections S.carrier
          (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app K ≫
        (derivedSectionsFunctorIsoBaseSections S).hom.app K :=
  rfl

/-- **The unit `Γ(S, 𝒦^•) ⟶ RΓ(S, 𝒦^•)` in the unbounded model**, the composite of the two
arrows of the left-hand column of the source's preceding diagram with the identification of the
two models. -/
def sectionsToBaseSections :
    Stacks.Cech.Linear.sectionsDerivedFunctor S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ ⟶
      CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ baseSections S :=
  Stacks.Cech.Linear.sectionsToDerivedNat S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ ≫
    (derivedSectionsFunctorIsoBaseSections S).hom

/-- The unit at one complex, with the two factors displayed; the companion of
`cechToBaseSections_app`. -/
theorem sectionsToBaseSections_app
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    (sectionsToBaseSections S).app K =
      Stacks.Cech.Linear.sectionsToDerived S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ K ≫
        (derivedSectionsFunctorIsoBaseSections S).hom.app K :=
  rfl

/-- **The pinning of the comparison.**  After the augmentation of [Stacks, Tag 07M9] the
comparison of Tag 08BN is the unit `Γ(S, 𝒦^•) ⟶ RΓ(S, 𝒦^•)`.  This is the `sections` field of
`Stacks.Cech.Linear.CechToDerivedSectionsSystem` carried through the model bridge; in particular
the composite does not depend on the covering. -/
theorem sectionsToTotalCechDerived_comp_cechToBaseSections
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    (Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤
          Ui hU).app K ≫ (cechToBaseSections S Ui hU).app K =
      (sectionsToBaseSections S).app K :=
  comp_comp_of_eq _ _ _ _
    (Stacks.Cech.Linear.sectionsToTotalCechDerived_comp_totalCechToDerivedSections
      S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU K)

/-- **On a bounded below complex of flasque modules the comparison of [Stacks, Tag 08BN] is
invertible in `D(A)`**, in the model the global cup product is stated in.  This is the
identification `Tot(Č^•(𝒰, 𝒦^•)) = RΓ(S, 𝒦^•)` that the proof of [Stacks, Tag 0FKV] reduces its
diagram to, in the form a consumer of that reduction needs it. -/
theorem isIso_cechToBaseSections_app_of_isFlasque
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))
    (hfl : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque) :
    IsIso ((cechToBaseSections S Ui hU).app K) :=
  isIso_comp_hom_app (derivedSectionsFunctorIsoBaseSections S) _
    (Stacks.Cech.Linear.isIso_totalCechToDerivedSections_app_of_isFlasque
      S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU K hfl)

/-- **On a bounded below complex of flasque modules the unit `Γ(S, 𝒦^•) ⟶ RΓ(S, 𝒦^•)` is
invertible in `D(A)`**, in the model the global cup product is stated in: the other half of the
identification the proof of [Stacks, Tag 0FKV] reduces its diagram to. -/
theorem isIso_sectionsToBaseSections_app_of_isFlasque
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))
    (hfl : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque) :
    IsIso ((sectionsToBaseSections S).app K) :=
  isIso_comp_hom_app (derivedSectionsFunctorIsoBaseSections S) _
    (Stacks.Cech.Linear.isIso_sectionsToDerived_of_isFlasque
      S.carrier (ringSheaf.{u, u, u} S.sheaf) ⊤ K hfl)

/-! ### The two legs of the square -/

variable (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- **The left-hand leg of the square of [Stacks, Tag 0FKV]**: the canonical map from the derived
tensor product over `A` to the ordinary total tensor complex, the Čech cup product of
[Stacks, Tag 07MB] at the sheaf-tensor coefficient pairing, and the comparison of
[Stacks, Tag 08BN] on `Tot(𝒦^• ⊗_{𝒪_S} ℳ^•)`.

The first arrow is the natural transformation `canonicalDerivedToTensorNatTrans`, not the K-flat
comparison of `CochainComplex.DerivedTensor.DerivedTensorProduct`: the latter is an `Iso` which
requires both complexes to be K-flat, and `Tot(Č^•(𝒰, 𝒦^•))` over `A` is not K-flat for an
arbitrary bounded below `𝒦^•`. -/
def cechLeftLeg :
    (Functor.uncurry.obj (tensorBase S)).obj
        (DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj K.1),
          DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj M.1)) ⟶
      (baseSections S).obj (DerivedCategory.Q.obj (tensorPlus S K M).1) :=
  canonicalDerivedToTensorComp (CoeffRing.{u} S.sheaf ⊤)
      ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj K.1)
      ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj M.1)
      ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
      (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU) ≫
    (cechToBaseSections S Ui hU).app (tensorPlus S K M)

/-- **The right-hand leg of the square of [Stacks, Tag 0FKV]**: the comparison of
[Stacks, Tag 08BN] in each tensor factor, the global cup product `μ` of Cohomology,
Section 0FKU at the canonical one-point comparison, and derived global sections of the canonical
map `𝒦^• ⊗^𝐋_{𝒪_S} ℳ^• ⟶ Tot(𝒦^• ⊗_{𝒪_S} ℳ^•)` of [Stacks, Tag 06YU]. -/
def cechRightLeg :
    (Functor.uncurry.obj (tensorBase S)).obj
        (DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj K.1),
          DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj M.1)) ⟶
      (baseSections S).obj (DerivedCategory.Q.obj (tensorPlus S K M).1) :=
  (Functor.uncurry.obj (tensorBase S)).map
      ((cechToBaseSections S Ui hU).app K ×ₘ (cechToBaseSections S Ui hU).app M) ≫
    (globalCupProduct (canonicalOnePointComparison S)).app
      (DerivedCategory.Q.obj K.1, DerivedCategory.Q.obj M.1) ≫
    (baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1))

/-- **The assertion of [Stacks, Tag 0FKV]**: the two legs of the square are equal in `D(A)`.
It holds for every pair of bounded below complexes, by
`Stacks.Cech.CupProductSquare.cupProductSquareCommutes`. -/
def CupProductSquareCommutes : Prop :=
  cechLeftLeg S Ui hU K M = cechRightLeg S Ui hU K M

/-! ### The right-hand column, reduced along the augmentation -/

/-- **The right-hand column of [Stacks, Tag 0FKV]'s square, precomposed with the Čech
augmentation of [Stacks, Tag 07M9] in both tensor factors, is the right-hand column of the
diagram the source displays just before the tag** -- the one whose top left corner is
`Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•)`, which is [Stacks, Tag 0FP3] for the morphism from `S` to a point.

This is half of the final paragraph of the source's proof: it holds with no flasqueness
hypothesis and with no hypothesis on `μ`, flasqueness entering only when one wants to *cancel*
the augmentation, which `isIso_sectionsToTotalCechDerived_of_isFlasque` licenses.  The other half
-- the same statement for the left-hand column -- is the augmentation square
`Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct`. -/
theorem sectionsToTotalCechDerived_comp_cechRightLeg :
    (Functor.uncurry.obj (tensorBase S)).map
          ((Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
              (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app K ×ₘ
            (Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
              (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app M) ≫
        cechRightLeg S Ui hU K M =
      (Functor.uncurry.obj (tensorBase S)).map
          ((sectionsToBaseSections S).app K ×ₘ (sectionsToBaseSections S).app M) ≫
        (globalCupProduct (canonicalOnePointComparison S)).app
          (DerivedCategory.Q.obj K.1, DerivedCategory.Q.obj M.1) ≫
        (baseSections S).map ((derivedToTensorNatTrans S).app (K.1, M.1)) :=
  map_prod_comp_of_eq (Functor.uncurry.obj (tensorBase S)) _ _ _ _ _ _ _
    (sectionsToTotalCechDerived_comp_cechToBaseSections S Ui hU K)
    (sectionsToTotalCechDerived_comp_cechToBaseSections S Ui hU M)

end Stacks.Cech.CupProductSquare

end
