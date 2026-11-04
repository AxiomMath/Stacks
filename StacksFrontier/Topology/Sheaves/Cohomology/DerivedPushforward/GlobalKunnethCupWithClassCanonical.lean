module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.CategoryTheory.AdjunctionBitensorMapPullback
public import StacksFrontier.CategoryTheory.BifunctorComparisonAssocTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductCanonicalInstances
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapAndCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapCanonical
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductComposition
import StacksCore.Tactic.StacksAttribute

/-!
# Remark 0G7W with no parameter

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `p`, `q` the projections of `X ×_S Y`,
`A = Γ(S, 𝒪_S)`, and `ξ ∈ Hⁱ(X, 𝒢)`.  Remark 0G7W of the Stacks project is the commutativity of

```
RΓ(X, ℱ)[-i] ⊗^𝐋_A RΓ(Y, ℰ) --ξ ⊗ 1--> RΓ(X, 𝒢 ⊗ ℱ) ⊗^𝐋_A RΓ(Y, ℰ)
           |                                            |
           v                                            v
RΓ(X ×_S Y, p^*ℱ ⊗ q^*ℰ)[-i] --p^*ξ--> RΓ(X ×_S Y, p^*(𝒢 ⊗ ℱ) ⊗ q^*ℰ)
```

in `D(A)`, with horizontal arrows cup product with a class (Remark 0G6W) and vertical arrows
the global Künneth map (Equation 36.23.0.2, Tag 0G7V); the source's proof is the associativity
of the global cup product (Lemma 0FP4).

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapAndCupProduct`
reduces the square to that associativity but carries as parameters the one-point comparisons on
`X` and `W`, the pullback map `π` with its compatibility `hπ` with the cup products (Lemma 0FP6),
and associativity constraints with their naturality and compatibility.  This file discharges
every one of them, so the square holds with no hypothesis, for the parameter-free global Künneth
map `kunnethGlobalMapSchemeCanonical` registered for Tag 0G7V.

## Main definitions

* `Stacks.Cohomology.KunnethCupWithClass.baseAssociator` — the associativity constraint of
  `⊗^𝐋_A`: that of Tag 0FPB on the one-point ringed space `({*}, A)`, read through the
  identification `D(A) = D({*}, A)` by which Section 0FKU defines the global cup product.
* `Stacks.Cohomology.KunnethCupWithClass.sectionsOverBaseComparison` — the one-point comparison
  of a space `c : V ⟶ S` over the base, with no parameter: the left adjoint of
  `RΓ(V, -) : D(𝒪_V) ⥤ D(A)` assembled from that of the base and `Lc^* ⊣ Rc_*`.
* `Stacks.Cohomology.KunnethCupWithClass.pullbackSections` — the pullback map
  `p^* : RΓ(X, K) ⟶ RΓ(W, Lp^*K)` on derived global sections.

## Main results

* `Stacks.Cohomology.KunnethCupWithClass.comparisonAssociative_sectionsOverBaseComparison` — the
  comparison is compatible with the associativity constraints (the input of Lemma 0FP4).
* `Stacks.Cohomology.KunnethCupWithClass.cupProductOverBase_sectionsOverBaseComparison` — the
  `A`-linear cup product on `V` is the global cup product of the base followed by the relative
  cup product of `c` (Lemma 0FP6 for `V ⟶ S ⟶ ({*}, A)`).
* `Stacks.Cohomology.KunnethCupWithClass.cupProductPullbackCompatible` — Lemma 0FP6 for the cup
  products on `X` and on `W` along `p`: the hypothesis `hπ` of the parametric statement.
* `Stacks.Cohomology.KunnethCupWithClass.kunnethOverBase_eq_kunnethGlobalMapCanonical` — pulling
  back and taking the cup product on `W`, the source's description of Equation 36.23.0.2, is the
  registered map of Tag 0G7V.
* `Stacks.Cohomology.KunnethCupWithClass.kunnethGlobalMapSchemeCanonical_cupWithClass` —
  **Remark 0G7W** at `X ×_S Y`.

## Implementation notes

*Generality.*  `𝒢`, `ℱ`, `ℰ` are arbitrary objects of the derived categories (the source's
quasi-coherent modules are the case of modules in degree zero), the tensor products are derived
— the arrows of Remark 0G6W and Equation 36.23.0.2 land in derived tensor products — and `S` is
an arbitrary scheme with `A = Γ(S, 𝒪_S)`; the source's affineness of `S` is not used.

*The identifications in the corners.*  `RΓ(X, ℱ)[-i]` is `A[-i] ⊗^𝐋_A RΓ(X, ℱ)` as in Remark
0G6W (`baseShiftTensorIso`), so the left vertical is the Künneth map tensored with `A[-i]` after
the associativity constraint `baseAssociator`; the source's silent identifications
`p^*(𝒢 ⊗ ℱ) = p^*𝒢 ⊗ p^*ℱ` (Tag 079U) and the rebracketing (Tag 0FPB) are the last two arrows of
the right-hand route.

*Why the constraint over `A` is read through `({*}, A)`.*  The global cup product of Section
0FKU is the relative cup product for the morphism to the one-point ringed space `({*}, A)`,
read through `D(A) = D({*}, A)`; Lemma 0FP4 for it needs the comparison of that identification
to carry the constraint of `D(A)` to the one of `D({*}, A)`.  Defining the constraint of `D(A)`
as the one carried over (`CategoryTheory.transportedAssociator`) makes this hold by
construction, and it is the unique constraint with this property
(`CategoryTheory.transportedAssociator_unique`).

## References

* [Stacks Project, Tag 0G7W](https://stacks.math.columbia.edu/tag/0G7W)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0G6W](https://stacks.math.columbia.edu/tag/0G6W)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.KunnethCupWithClass

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing

variable (S : RingedSpace.{u, u})

/-! ### The associativity constraint of `⊗^𝐋_A` through `D(A) = D({*}, A)` -/

/-- The one-point identification `D(A) ⥤ D(𝒪_{({*}, A)})` is fully faithful: it is restriction of
scalars along a ring isomorphism followed by the identification of modules with sheaves of
modules on the point, both equivalences of abelian categories, read on derived categories. -/
def baseToPointFullyFaithful : (baseToPoint S).FullyFaithful :=
  haveI : (basePointRestrict S).functor.mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory (basePointRestrict S)
  haveI : (basePointExtension S).IsEquivalence :=
    Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory (onePointSectionsEquivalence (baseRing S))
  Functor.FullyFaithful.ofFullyFaithful (baseToPoint S)

/-- The tensor comparison of the one-point identification, as the isomorphism of bifunctors
it is: restriction of scalars along a ring isomorphism and the one-point identification both
carry the derived tensor product to the derived tensor product. -/
def baseTensorComparisonIso :
    Functor.uncurry.obj (tensorBase S) ⋙ baseToPoint S ≅
      (baseToPoint S).prod (baseToPoint S) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor (basePoint S).sheaf) :=
  Functor.isoWhiskerRight
      (CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorIso
        (basePointCommRingEquiv S)) (basePointExtension S) ≪≫
    Functor.isoWhiskerLeft (((basePointRestrict S).functor.mapDerivedCategory).prod
      ((basePointRestrict S).functor.mapDerivedCategory))
      (onePointDerivedTensorIso ↥(baseRing S))

/-- The isomorphism `baseTensorComparisonIso` is the comparison `baseTensorComparison`. -/
theorem baseTensorComparisonIso_hom : (baseTensorComparisonIso S).hom = baseTensorComparison S :=
  rfl

/-- **The associativity constraint of the derived tensor product over `A = Γ(S, 𝒪_S)`** that
the source uses: the associativity constraint of Tag 0FPB on the one-point ringed space
`({*}, A)`, carried to `D(A)` along the identification `D(A) = D({*}, A)` of Section 0FKU. -/
def baseAssociator (P Q Z : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    ((tensorBase S).obj (((tensorBase S).obj P).obj Q)).obj Z ⟶
      ((tensorBase S).obj P).obj (((tensorBase S).obj Q).obj Z) :=
  transportedAssociator (baseToPointFullyFaithful S) (Functor.uncurry.obj (tensorBase S))
    (Functor.uncurry.obj (derivedTensorProductFunctor (basePoint S).sheaf))
    (baseTensorComparisonIso S) (derivedAssociator (basePoint S)) P Q Z

/-- The associativity constraint over `A` is natural in all three variables. -/
theorem baseAssociator_naturality
    {P P' Q Q' Z Z' : DerivedCategory (ModuleCat.{u} (baseRing S))} (k : P ⟶ P')
    (l : Q ⟶ Q') (m : Z ⟶ Z') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((Functor.uncurry.obj (tensorBase S)).map (k ×ₘ l) ×ₘ m) ≫ baseAssociator S P' Q' Z' =
      baseAssociator S P Q Z ≫
        (Functor.uncurry.obj (tensorBase S)).map
          (k ×ₘ (Functor.uncurry.obj (tensorBase S)).map (l ×ₘ m)) :=
  transportedAssociator_naturality (baseToPointFullyFaithful S) _ _ _ _
    (fun u v w => derivedAssociator_naturality (basePoint S) u v w) k l m

/-- The tensor comparison of the one-point identification is compatible with the associativity
constraints. -/
theorem comparisonAssociative_baseTensorComparison :
    ComparisonAssociative (Functor.uncurry.obj (tensorBase S))
      (Functor.uncurry.obj (derivedTensorProductFunctor (basePoint S).sheaf))
      (baseTensorComparison S) (baseAssociator S) (derivedAssociator (basePoint S)) :=
  comparisonAssociative_transportedAssociator (baseToPointFullyFaithful S) _ _
    (baseTensorComparisonIso S) _

/-- **The canonical one-point comparison is associative**: the comparison
`L(x ⊗^𝐋_A y) ⟶ Lx ⊗^𝐋_{𝒪_S} Ly` of the left adjoint of `RΓ(S, -)` carries the associativity
constraint over `A` to that of Tag 0FPB on `D(𝒪_S)`. -/
theorem comparisonAssociative_onePointComparisonCanonical :
    ComparisonAssociative (L := (onePointComparisonCanonical S).pullback)
      (Functor.uncurry.obj (tensorBase S))
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
      (onePointComparisonCanonical S).tensorComparison (baseAssociator S)
      (derivedAssociator S) :=
  (comparisonAssociative_baseTensorComparison S).comp
    (pullbackTensorComparisonAssociative (toBasePoint S))

/-! ### The `A`-linear cup product on a space over the base -/

variable {S} {V : RingedSpace.{u, u}}

/-- **The one-point comparison for a space `c : V ⟶ S` over the base, with no parameter**: the
left adjoint `Lc^* ∘ L` of `RΓ(V, -) : D(𝒪_V) ⥤ D(A)`, the composite of the adjunction of the
base with `Lc^* ⊣ Rc_*` read through the Leray isomorphism, and the composite comparison. -/
def sectionsOverBaseComparison (c : V ⟶ S) : SectionsOverBaseComparison c where
  pullback := (onePointComparisonCanonical S).pullback ⋙ derivedPullback c
  adjunction :=
    ((onePointComparisonCanonical S).adjunction.comp (derivedAdjunction c)).ofNatIsoRight
      (lerayIso c)
  tensorComparison :=
    Functor.whiskerRight (onePointComparisonCanonical S).tensorComparison (derivedPullback c) ≫
      Functor.whiskerLeft
        ((onePointComparisonCanonical S).pullback.prod (onePointComparisonCanonical S).pullback)
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison c)

/-- The comparison of `sectionsOverBaseComparison c` is associative. -/
theorem comparisonAssociative_sectionsOverBaseComparison (c : V ⟶ S) :
    ComparisonAssociative (L := (sectionsOverBaseComparison c).pullback)
      (Functor.uncurry.obj (tensorBase S))
      (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
      (sectionsOverBaseComparison c).tensorComparison (baseAssociator S)
      (derivedAssociator V) :=
  (comparisonAssociative_onePointComparisonCanonical S).comp
    (pullbackTensorComparisonAssociative c)

section CupOverBase

variable (c : V ⟶ S)

/-- **The `A`-linear cup product on `V` is the global cup product on the base followed by the
relative cup product of `c`** (Cohomology, Lemma 0FP6 for `V ⟶ S ⟶ ({*}, A)`): read through the
Leray isomorphisms `RΓ(S, Rc_* -) ≅ RΓ(V, -)`, it is `μ_S` at `(Rc_*K, Rc_*M)` followed by
`RΓ(S, -)` of the relative cup product of Tag 0B68. -/
theorem cupProductOverBase_sectionsOverBaseComparison
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    cupProductOverBase (sectionsOverBaseComparison c) K M =
      (Functor.uncurry.obj (tensorBase S)).map
          ((lerayIso c).inv.app K ×ₘ (lerayIso c).inv.app M) ≫
        (globalCupProductCanonical S).app ((derivedPushforward c).obj K,
          (derivedPushforward c).obj M) ≫
        (baseSections S).map (relativeCupProduct c K M) ≫
          (lerayIso c).hom.app (((derivedTensorProductFunctor V.sheaf).obj K).obj M) := by
  have h₁ := Stacks.Cohomology.AdjunctionBitensorPullback.adjunctionBitensorMap_ofNatIsoRight
    ((onePointComparisonCanonical S).adjunction.comp (derivedAdjunction c)) (lerayIso c)
    (Functor.uncurry.obj (tensorBase S))
    (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
    (sectionsOverBaseComparison c).tensorComparison K M
  have h₂ : adjunctionBitensorMap
        ((onePointComparisonCanonical S).adjunction.comp (derivedAdjunction c))
        (Functor.uncurry.obj (tensorBase S))
        (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
        (sectionsOverBaseComparison c).tensorComparison K M =
      (globalCupProductCanonical S).app ((derivedPushforward c).obj K,
          (derivedPushforward c).obj M) ≫
        (baseSections S).map (relativeCupProduct c K M) :=
    adjunctionBitensorMap_comp (onePointComparisonCanonical S).adjunction
    (derivedAdjunction c) (Functor.uncurry.obj (tensorBase S))
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf))
    (onePointComparisonCanonical S).tensorComparison
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison c) K M
  rw [h₂] at h₁
  simp only [Category.assoc] at h₁
  exact h₁

end CupOverBase

/-! ### The pullback map on derived global sections -/

section Pullback

variable {X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- The adjoint `Ra_*K ⟶ Rf_*Lp^*K` of the counit leg of Equation 36.23.0.1: the pullback map
`K ⟶ Rp_*Lp^*K` pushed forward to the base. -/
def pullbackLeg (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPushforward a).obj K ⟶ (derivedPushforward f).obj ((derivedPullback p).obj K) :=
  (derivedAdjunction f).homEquiv _ _
    ((Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p f hp).app K)

/-- **The pullback map on derived global sections** `RΓ(X, K) ⟶ RΓ(W, Lp^*K)` in `D(A)`:
`RΓ(X, K) = RΓ(S, Ra_*K) ⟶ RΓ(S, Rf_*Lp^*K) = RΓ(W, Lp^*K)`, the map `p^*` of the source. -/
def pullbackSections (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (sectionsOverBase a).obj K ⟶ (sectionsOverBase f).obj ((derivedPullback p).obj K) :=
  (lerayIso a).inv.app K ≫ (baseSections S).map (pullbackLeg a p f hp K) ≫
    (lerayIso f).hom.app ((derivedPullback p).obj K)

/-- The relative Künneth morphism of Tag 0FLP is the two pullback legs followed by the relative
cup product of Tag 0B68 on `W`. -/
theorem kunnethMap_eq_relativeCupProduct
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M =
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
          (pullbackLeg a p f hp K ×ₘ pullbackLeg b q f hq M) ≫
        relativeCupProduct f ((derivedPullback p).obj K) ((derivedPullback q).obj M) :=
  Stacks.Cohomology.AdjunctionBitensorPullback.kunnethAdjunctionBitensorMap_eq _ _ _ _ _ _ K M

/-- **The pullback maps followed by the `A`-linear cup product on `W`**, written on the base:
the Leray isomorphisms, the global cup product of the base, and `RΓ(S, -)` of the pullback legs
followed by the relative cup product of `f`. -/
theorem pullbackSections_cupProductOverBase
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (Functor.uncurry.obj (tensorBase S)).map
          (pullbackSections a p f hp K ×ₘ pullbackSections b q f hq M) ≫
        cupProductOverBase (sectionsOverBaseComparison f) ((derivedPullback p).obj K)
          ((derivedPullback q).obj M) =
      (Functor.uncurry.obj (tensorBase S)).map
          ((lerayIso a).inv.app K ×ₘ (lerayIso b).inv.app M) ≫
        (globalCupProductCanonical S).app ((derivedPushforward a).obj K,
          (derivedPushforward b).obj M) ≫
        (baseSections S).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
              (pullbackLeg a p f hp K ×ₘ pullbackLeg b q f hq M) ≫
            relativeCupProduct f ((derivedPullback p).obj K) ((derivedPullback q).obj M)) ≫
          (lerayIso f).hom.app _ := by
  rw [cupProductOverBase_sectionsOverBaseComparison]
  exact Stacks.Cohomology.AdjunctionBitensorPullback.sections_comp_cup _ _ _
    (globalCupProductCanonical S) (lerayIso a) (lerayIso b) (lerayIso f) _ _ _

/-- **The vertical arrows of the square are the global Künneth map of Tag 0G7V**: pulling back
to `W` and taking the `A`-linear cup product there — the source's description of Equation
36.23.0.2 — is `kunnethGlobalMapCanonical`, the map registered for Tag 0G7V. -/
theorem kunnethOverBase_eq_kunnethGlobalMapCanonical
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethOverBase (sectionsOverBaseComparison f) (pullbackSections a p f hp)
        (pullbackSections b q f hq) K M =
      kunnethGlobalMapCanonical a b p q f hp hq K M := by
  rw [kunnethGlobalMapCanonical_eq, kunnethGlobalMap_eq, kunnethMap_eq_relativeCupProduct]
  exact pullbackSections_cupProductOverBase a b p q f hp hq K M

/-! ### Compatibility of the cup products with pullback (Lemma 0FP6) -/

/-- The counit leg for `p ≫ a`, written out: the composition isomorphism of Tag 0D5S followed
by `Lp^*` of the counit of `La^* ⊣ Ra_*`. -/
theorem pullbackCounitLeg_app_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p (p ≫ a) rfl).app K =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv.app
          ((derivedPushforward a).obj K) ≫
        (derivedPullback p).map ((derivedAdjunction a).counit.app K) := by
  simp only [Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg,
    Stacks.Cohomology.DerivedKunneth.pullbackCounitLegComp, NatTrans.comp_app, eqToHom_refl,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
  exact congrArg (fun z => _ ≫ z) (Category.comp_id _)

/-- **The relative form of Lemma 0FP6 at the pullback legs.**  The two pullback legs followed by
the relative cup product of `p ≫ a` on `W` are the relative cup product of `a` followed by the
pullback leg and the comparison of Tag 079U. -/
theorem pullbackLeg_relativeCupProduct
    (U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
          (pullbackLeg a p f hp U ×ₘ pullbackLeg a p f hp V) ≫
        relativeCupProduct f ((derivedPullback p).obj U) ((derivedPullback p).obj V) =
      relativeCupProduct a U V ≫
        pullbackLeg a p f hp (((derivedTensorProductFunctor X.sheaf).obj U).obj V) ≫
          (derivedPushforward f).map
            ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison p).app
              (U, V)) := by
  subst hp
  exact Stacks.Cohomology.AdjunctionBitensorPullback.legs_adjunctionBitensorMap
    (derivedAdjunction a) (derivedAdjunction (p ≫ a)) (derivedPullback p)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a) _ _ _ _ _ _
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp p a)
    (fun K => (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p (p ≫ a) rfl).app K)
    (pullbackCounitLeg_app_comp a p) U V

/-- **Cohomology, Lemma 0FP6 for the `A`-linear cup products on `X` and on `W`.**  For
`p ≫ a = f`, pulling back along `p` is compatible with the cup products on `X` and on `W`, the
right-hand route being continued by the comparison of Tag 079U. -/
theorem cupProductPullbackCompatible :
    CupProductPullbackCompatible (sectionsOverBaseComparison a) (sectionsOverBaseComparison f)
      (pullbackSections a p f hp) := by
  intro U V
  rw [cupProductOverBase_sectionsOverBaseComparison, cupProductOverBase_sectionsOverBaseComparison]
  exact Stacks.Cohomology.AdjunctionBitensorPullback.sections_cup_compatible _ _ _
    (globalCupProductCanonical S) (lerayIso a) (lerayIso f) _ _ _ _ _ _
    (pullbackLeg_relativeCupProduct a p f hp U V)

/-! ### Remark 0G7W -/

/-- Replacing two morphisms by equal ones in an equation of composites, one of them under a
functor. -/
private lemma eq_of_eq_of_eq {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {X Y Z W V : C} {P Q : D} (t : X ⟶ Y) {k k' : Y ⟶ Z} (m : Z ⟶ W) (s₁ : X ⟶ V)
    (s₂ : V ⟶ F.obj P) {l l' : P ⟶ Q} (s₃ : F.obj Q ⟶ W) (e : k = k') (e' : l = l')
    (h : t ≫ k ≫ m = s₁ ≫ s₂ ≫ F.map l ≫ s₃) : t ≫ k' ≫ m = s₁ ≫ s₂ ≫ F.map l' ≫ s₃ := by
  subst e e'
  exact h

/-- **Remark 0G7W, with no parameter**, for spaces over a base. -/
theorem kunnethGlobalMapCanonical_cupWithClass
    (𝒢 ℱ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (ℰ : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i : ℤ)
    (ξ : baseShift S i ⟶ (sectionsOverBase a).obj 𝒢) :
    ((tensorBase S).map (cupWithClassOverBase (sectionsOverBaseComparison a) 𝒢 ℱ i ξ)).app
            ((sectionsOverBase b).obj ℰ) ≫
        kunnethGlobalMapCanonical a b p q f hp hq
            (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ℰ ≫
          (sectionsOverBase f).map
              ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
                (pullbackTensorComparisonApp p 𝒢 ℱ ×ₘ 𝟙 ((derivedPullback q).obj ℰ))) ≫
            (sectionsOverBase f).map
              (derivedAssociator W ((derivedPullback p).obj 𝒢) ((derivedPullback p).obj ℱ)
                ((derivedPullback q).obj ℰ)) =
      (Functor.uncurry.obj (tensorBase S)).map
          ((baseShiftTensorIso S i ((sectionsOverBase a).obj ℱ)).inv ×ₘ
            𝟙 ((sectionsOverBase b).obj ℰ)) ≫
        baseAssociator S (baseShift S i) ((sectionsOverBase a).obj ℱ)
            ((sectionsOverBase b).obj ℰ) ≫
          ((tensorBase S).obj (baseShift S i)).map
              (kunnethGlobalMapCanonical a b p q f hp hq ℱ ℰ) ≫
            (baseShiftTensorIso S i
              ((sectionsOverBase f).obj
                (((derivedTensorProductFunctor W.sheaf).obj
                  ((derivedPullback p).obj ℱ)).obj ((derivedPullback q).obj ℰ)))).hom ≫
              cupWithClassOverBase (sectionsOverBaseComparison f) ((derivedPullback p).obj 𝒢)
                (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj ℱ)).obj
                  ((derivedPullback q).obj ℰ)) i (ξ ≫ pullbackSections a p f hp 𝒢) := by
  refine eq_of_eq_of_eq ((tensorBase S).obj (baseShift S i)) _ _ _ _ _
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a b p q f hp hq
      (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ℰ)
    (kunnethOverBase_eq_kunnethGlobalMapCanonical a b p q f hp hq ℱ ℰ) ?_
  exact kunnethOverBase_cupWithClassOverBase (sectionsOverBaseComparison a)
    (sectionsOverBaseComparison f) (pullbackSections a p f hp) (pullbackSections b q f hq) 𝒢 ℱ
    ℰ i (baseAssociator S) (derivedAssociator W)
    (fun k l m => baseAssociator_naturality S k l m)
    (fun k l m => derivedAssociator_naturality W k l m)
    (comparisonAssociative_sectionsOverBaseComparison f)
    (cupProductPullbackCompatible a p f hp) ξ


/-! ### Classes and their pullbacks -/

/-- **The representative of the image of a class is the representative followed by the map**:
for a class `ξ ∈ Hⁱ(V, K)` and a morphism `g : RΓ(V, K) ⟶ RΓ(V', K')` in `D(A)`, the morphism
`A[-i] ⟶ RΓ(V', K')` representing `Hⁱ(g)(ξ)` is the one representing `ξ` followed by `g`. -/
theorem classOverBase_comp_homology {V V' : RingedSpace.{u, u}} (c : V ⟶ S) (c' : V' ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing V'))) (i : ℤ)
    (g : (sectionsOverBase c).obj K ⟶ (sectionsOverBase c').obj K')
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModuleOverBase c K i) :
    classOverBase c' K' i
        (ξ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map g) =
      classOverBase c K i ξ ≫ g := by
  apply (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
    ((sectionsOverBase c').obj K') i (baseRing S)).injective
  unfold classOverBase
  rw [LinearEquiv.apply_symm_apply, DerivedCategory.homologyFromSingleLinearEquiv_comp,
    LinearEquiv.apply_symm_apply]

end Pullback

/-! ### Remark 0G7W at the fibre product of two schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **Remark 0G7W.**  Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let
`p : X ×_S Y ⟶ X` and `q : X ×_S Y ⟶ Y` be the projections, and set `A = Γ(S, 𝒪_S)`.  Let
`𝒢, ℱ ∈ D(𝒪_X)` and `ℰ ∈ D(𝒪_Y)` — for instance quasi-coherent modules placed in degree
zero — and let `ξ ∈ Hⁱ(X, 𝒢)`, with pullback `p^*ξ ∈ Hⁱ(X ×_S Y, Lp^*𝒢)`, represented by the
morphism `A[-i] ⟶ RΓ(X, 𝒢)` representing `ξ` followed by the pullback map
`p^* : RΓ(X, 𝒢) ⟶ RΓ(X ×_S Y, Lp^*𝒢)` (that this represents the class `Hⁱ(p^*)(ξ)` is
`Stacks.Cohomology.KunnethCupWithClass.classOverBase_comp_homology`).  Then the square

```
RΓ(X, ℱ)[-i] ⊗^𝐋_A RΓ(Y, ℰ) --ξ ⊗ 1--> RΓ(X, 𝒢 ⊗ ℱ) ⊗^𝐋_A RΓ(Y, ℰ)
           |                                            |
           v                                            v
RΓ(X ×_S Y, Lp^*ℱ ⊗ Lq^*ℰ)[-i] --p^*ξ--> RΓ(X ×_S Y, Lp^*(𝒢 ⊗ ℱ) ⊗ Lq^*ℰ)
```

commutes in `D(A)`.  The horizontal arrows are cup product with a class, Remark 0G6W, for the
`A`-linear global cup products of Section 0FKU on `X` and on `X ×_S Y`; the vertical arrows are
the global Künneth map of Equation 36.23.0.2, `kunnethGlobalMapSchemeCanonical` (Tag 0G7V),
shifted by `[-i]` through the source's identification `M[-i] = A[-i] ⊗^𝐋_A M`.  Nothing is a
parameter: the cup products, the pullback map, the associativity constraint `baseAssociator`
of `⊗^𝐋_A` (that of `D({*}, A)` read through `D(A) = D({*}, A)`, as in Section 0FKU) and that
of `⊗^𝐋_{𝒪}` (Tag 0FPB) are all canonical.  The two identifications the source makes silently in
the bottom-right corner, `Lp^*(𝒢 ⊗ ℱ) = Lp^*𝒢 ⊗ Lp^*ℱ` (Tag 079U) and the rebracketing, are
the last two arrows of the right-hand route.  No quasi-coherence, affineness or finiteness
hypothesis is needed. -/
@[stacks 0G7W]
theorem kunnethGlobalMapSchemeCanonical_cupWithClass
    (𝒢 ℱ : DerivedCategory X.Modules) (ℰ : DerivedCategory Y.Modules) (i : ℤ)
    (ξ : ModuleCat.of (baseRing S.toRingedSpace) (baseRing S.toRingedSpace) ⟶
      cohomologyModuleOverBase a.toLRSHom.toShHom 𝒢 i) :
    ((tensorBase S.toRingedSpace).map
          (cupWithClassOverBase (sectionsOverBaseComparison a.toLRSHom.toShHom) 𝒢 ℱ i
            (classOverBase a.toLRSHom.toShHom 𝒢 i ξ))).app
          ((sectionsOverBase b.toLRSHom.toShHom).obj ℰ) ≫
        kunnethGlobalMapSchemeCanonical a b
            (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝒢).obj ℱ) ℰ ≫
          (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).map
              ((Functor.uncurry.obj
                  (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf)).map
                (pullbackTensorComparisonApp (pullback.fst a b).toLRSHom.toShHom 𝒢 ℱ ×ₘ
                  𝟙 ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj ℰ))) ≫
            (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).map
              (derivedAssociator (pullback a b).toRingedSpace
                ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj 𝒢)
                ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj ℱ)
                ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj ℰ)) =
      (Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
          ((baseShiftTensorIso S.toRingedSpace i
              ((sectionsOverBase a.toLRSHom.toShHom).obj ℱ)).inv ×ₘ
            𝟙 ((sectionsOverBase b.toLRSHom.toShHom).obj ℰ)) ≫
        baseAssociator S.toRingedSpace (baseShift S.toRingedSpace i)
            ((sectionsOverBase a.toLRSHom.toShHom).obj ℱ)
            ((sectionsOverBase b.toLRSHom.toShHom).obj ℰ) ≫
          ((tensorBase S.toRingedSpace).obj (baseShift S.toRingedSpace i)).map
              (kunnethGlobalMapSchemeCanonical a b ℱ ℰ) ≫
            (baseShiftTensorIso S.toRingedSpace i
              ((sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
                (((derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf).obj
                  ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj ℱ)).obj
                    ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj ℰ)))).hom ≫
              cupWithClassOverBase
                (sectionsOverBaseComparison (pullback.fst a b ≫ a).toLRSHom.toShHom)
                ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj 𝒢)
                (((derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf).obj
                    ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj ℱ)).obj
                  ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj ℰ)) i
                (classOverBase a.toLRSHom.toShHom 𝒢 i ξ ≫
                  pullbackSections a.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom
                    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl 𝒢) :=
  kunnethGlobalMapCanonical_cupWithClass a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl (toShHom_pullback_condition a b) 𝒢 ℱ ℰ i
    (classOverBase a.toLRSHom.toShHom 𝒢 i ξ)

end Schemes

end Stacks.Cohomology.KunnethCupWithClass
