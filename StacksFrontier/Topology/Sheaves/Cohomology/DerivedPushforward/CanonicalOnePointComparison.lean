module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointDerivedTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical one-point comparison on an arbitrary ringed space

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`.
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison S` is the input of the global cup
product of Cohomology, Section 0FKU: a functor `L : D(A) ⥤ D(𝒪_S)`, an adjunction
`L ⊣ RΓ(S, -)`, and a comparison of bifunctors `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`.

This file constructs such a comparison for an **arbitrary** ringed space, with an **invertible**
tensor comparison. It is the one attached to the morphism of ringed spaces `π : S ⟶ ({*}, A)` of
Stacks 01BH: `L` is `Lπ^*` read on `D(A)` through the one-point identification
`Mod(A) ≌ Mod(𝒪_{({*}, A)})`, the adjunction is `Lπ^* ⊣ Rπ_*` of Stacks 079W composed with that
identification and with the Leray isomorphism of Stacks 0D5W, and the tensor comparison is the
one-point comparison of derived tensor products followed by the derived pullback–tensor
comparison of Stacks 079U. In particular the tensor comparison is not the zero morphism as soon
as `RΓ(S, -)` is nonzero at a single object.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.toCoeffPoint` — the morphism of ringed spaces
  `π : S ⟶ ({*}, Γ(S, 𝒪_S))` whose structure map on global sections is the identity.
* `Stacks.Cohomology.DerivedGlobalCupProduct.PointPresentation` — the three data of a one-point
  comparison, stated over an arbitrary ring `A` and an arbitrary right adjoint, with the tensor
  comparison asked for as an *isomorphism*.
* `Stacks.Cohomology.DerivedGlobalCupProduct.canonicalOnePointComparison` — **the canonical
  one-point comparison** on an arbitrary ringed space.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.baseRing_coefficientPoint` — the global functions of
  the coefficient point of `A` are `A`, as an equality of rings and not merely an isomorphism.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isIso_canonicalOnePointComparison_tensorComparison` —
  **the tensor comparison of the canonical one-point comparison is invertible.**
* `Stacks.Cohomology.DerivedGlobalCupProduct.canonicalOnePointComparison_tensorComparison_ne_zero`
  — hence it is not the zero morphism of bifunctors, on any ringed space whose derived global
  sections do not vanish identically.

## Implementation notes

The structure sheaf of the coefficient point is the skyscraper sheaf, so its ring of global
sections is `if * ∈ ⊤ then A else terminal`. That term is *equal* to `A`
(`baseRing_coefficientPoint`) but not definitionally equal to it, the decidability instance in
the `if` being classical, while `OnePointComparison S` asks for `D(Γ(S, 𝒪_S))`. Rather than
compare the two rings by a restriction of scalars, the data are bundled into `PointPresentation`,
which is transported along the *equality* of the two rings in one step.

`PointPresentation.tensorIso` is an isomorphism rather than a bare morphism of bifunctors, so
what reaches `OnePointComparison.tensorComparison` is the underlying morphism of an isomorphism.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.SiteCohomologyPresheaf
open Stacks.DerivedTensor.RingedSite

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The derived category of modules over a ring, along an equality of rings -/

section Transport

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- The identity functor of an abelian category induces the identity of its derived category. -/
def mapDerivedCategoryIdIso (E : Type*) [Category E] [Abelian E]
    [HasDerivedCategory.{u} E] :
    (𝟭 E).mapDerivedCategory ≅ 𝟭 (DerivedCategory E) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso E (ComplexShape.up ℤ))
    ((𝟭 E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q (𝟭 E).mapDerivedCategory (𝟭 _)
    (Functor.leftUnitor DerivedCategory.Q)

/-- Restriction of scalars along the identity ring map induces the identity of the derived
category of modules. -/
def restrictScalarsIdMapDerivedCategoryIso (A : CommRingCat.{u}) :
    (ModuleCat.restrictScalars.{u} (RingHom.id ↥A)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
      (ModuleCat.restrictScalars.{u} (RingHom.id ↥A)) (𝟭 _) (Iso.refl _) ≪≫
    mapDerivedCategoryIdIso (ModuleCat.{u} A)

/-- **Transport along an equality of rings** of a functor with values in the derived category of
modules over that ring. -/
def transportFunctor {A B : CommRingCat.{u}} (h : A = B)
    (F : C ⥤ DerivedCategory (ModuleCat.{u} A)) : C ⥤ DerivedCategory (ModuleCat.{u} B) :=
  h ▸ F

/-- Transport along the reflexivity equality `A = A` is the identity on functors. -/
@[simp] theorem transportFunctor_rfl {A : CommRingCat.{u}}
    (F : C ⥤ DerivedCategory (ModuleCat.{u} A)) : transportFunctor (rfl : A = A) F = F :=
  rfl

/-- The transport carries an isomorphism of functors to an isomorphism of their transports. -/
def transportIso {A B : CommRingCat.{u}} (h : A = B)
    {F G : C ⥤ DerivedCategory (ModuleCat.{u} A)} (e : F ≅ G) :
    transportFunctor h F ≅ transportFunctor h G := by
  subst h; exact e

/-- The transport leaves a precomposition alone. -/
theorem transportFunctor_comp {A B : CommRingCat.{u}} (h : A = B) (F : C ⥤ D)
    (G : D ⥤ DerivedCategory (ModuleCat.{u} A)) :
    transportFunctor h (F ⋙ G) = F ⋙ transportFunctor h G := by
  subst h; rfl

/-- Restriction of scalars along a ring map that the equality `h : A = B` makes the identity
becomes, after transport along `h`, the identity of the derived category. -/
def transportRestrictScalarsIsoId {A B : CommRingCat.{u}} (h : A = B) (ψ : ↥A →+* ↥B)
    (hψ : HEq ψ (RingHom.id ↥A)) :
    transportFunctor h ((ModuleCat.restrictScalars.{u} ψ).mapDerivedCategory) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} B)) := by
  subst h
  obtain rfl : ψ = RingHom.id ↥A := eq_of_heq hψ
  exact restrictScalarsIdMapDerivedCategoryIso A

/-- A functor to `D(B)` followed by an endofunctor which the transport along `h : A = B` makes
the identity, and then transported back along `h`, is the functor itself. -/
def transportCompIsoId {A B : CommRingCat.{u}} (h : A = B)
    (T : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A))
    (hT : transportFunctor h T ≅ 𝟭 (DerivedCategory (ModuleCat.{u} B)))
    (F : C ⥤ DerivedCategory (ModuleCat.{u} B)) :
    transportFunctor h (F ⋙ T) ≅ F :=
  eqToIso (transportFunctor_comp h F T) ≪≫ Functor.isoWhiskerLeft F hT ≪≫ F.rightUnitor

/-- The ring map underlying an `eqToHom` of rings is the identity, up to the equality of its
source and target. -/
theorem heq_forget₂_eqToHom_hom {A B : CommRingCat.{u}} (h : A = B) :
    HEq ((forget₂ CommRingCat.{u} RingCat.{u}).map (eqToHom h)).hom (RingHom.id ↥A) := by
  cases h; simp

end Transport

/-! ### The coefficient point of the ring of global functions -/

section CoefficientPoint

attribute [local instance] Stacks.AssociatedSheaf.pointMemDecidable

/-- **The global functions of the coefficient point of `A` are `A`**, as an equality of rings. -/
theorem baseRing_coefficientPoint (A : CommRingCat.{u}) : baseRing (coefficientPoint A) = A := by
  show (skyscraperPresheaf (X := TopCat.of PUnit.{u + 1}) PUnit.unit A).obj (op ⊤) = A
  rw [skyscraperPresheaf_obj]
  exact if_pos trivial

end CoefficientPoint

variable (S : RingedSpace.{u, u})

/-- **The morphism of ringed spaces `π : S ⟶ ({*}, Γ(S, 𝒪_S))`** of Stacks 01BH whose structure
map on global sections is the identity. -/
abbrev toCoeffPoint : S ⟶ onePointRingedSpace ↥(baseRing S) :=
  toCoefficientPoint' S (RingHom.id ↥(baseRing S))

/-- The ring of global functions of the coefficient point of `Γ(S, 𝒪_S)` is `Γ(S, 𝒪_S)`. -/
theorem baseRing_coeffPoint : baseRing (onePointRingedSpace ↥(baseRing S)) = baseRing S :=
  baseRing_coefficientPoint (CommRingCat.of ↥(baseRing S))

/-- The structure map of `π` on global sections. -/
abbrev coeffStructMap := ((structureSheafHom (toCoeffPoint S)).hom.app (op ⊤)).hom

/-- The ring map `coeffStructMap S`, with the point's ring of global functions spelled as a
`CommRingCat` object; the two spellings are definitionally equal. -/
abbrev coeffStructMapComm : ↥(baseRing (onePointRingedSpace ↥(baseRing S))) →+* ↥(baseRing S) :=
  coeffStructMap S

/-- **Restriction of scalars along `π^♯` on global sections**, from `Γ(S, 𝒪_S)`-modules to
modules over the point's ring of global functions. -/
def coeffRestrict :
    ModuleCat.{u} ((structureSheafRing S).obj.obj (op ⊤)) ⥤
      ModuleCat.{u} ((structureSheafRing (onePointRingedSpace ↥(baseRing S))).obj.obj (op ⊤)) :=
  ModuleCat.restrictScalars (coeffStructMap S)

/-- Restriction of scalars along `π^♯` is additive. -/
instance coeffRestrict_additive : (coeffRestrict S).Additive where
  map_add := rfl

/-- Restriction of scalars along `π^♯` preserves finite limits. -/
instance coeffRestrict_preservesFiniteLimits : PreservesFiniteLimits (coeffRestrict S) :=
  inferInstanceAs
    (PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (coeffStructMapComm S)))

/-- Restriction of scalars along `π^♯` preserves finite colimits. -/
instance coeffRestrict_preservesFiniteColimits : PreservesFiniteColimits (coeffRestrict S) :=
  inferInstanceAs
    (PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (coeffStructMapComm S)))

/-- **The structure map of `π` on global sections is the canonical identification** of the
skyscraper's sections with the ring, `eqToHom (baseRing_coeffPoint S)`. -/
theorem structureSheafHom_toCoeffPoint_app_top :
    (structureSheafHom (toCoeffPoint S)).hom.app (op ⊤) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map (eqToHom (baseRing_coeffPoint S)) := by
  refine (congrArg (fun g ↦ (forget₂ CommRingCat.{u} RingCat.{u}).map g)
    (skyscraperDesc_app_top (R := CommRingCat.of ↥(baseRing S))
      (toPointMap S.carrier _* S.presheaf)
      (fun _ h ↦ S.sheaf.isTerminalOfEqEmpty (toPointMap_obj_eq_bot h))
      (CommRingCat.ofHom (RingHom.id ↥(baseRing S))))).trans ?_
  exact congrArg (fun g ↦ (forget₂ CommRingCat.{u} RingCat.{u}).map g) (Category.comp_id _)

/-- The structure map of `π` on global sections is the identity, once the two rings are
identified. -/
theorem heq_coeffStructMap :
    HEq (coeffStructMap S) (RingHom.id ↥(baseRing (onePointRingedSpace ↥(baseRing S)))) := by
  rw [show coeffStructMap S =
    ((forget₂ CommRingCat.{u} RingCat.{u}).map (eqToHom (baseRing_coeffPoint S))).hom from
      congrArg RingCat.Hom.hom (structureSheafHom_toCoeffPoint_app_top S)]
  exact heq_forget₂_eqToHom_hom (baseRing_coeffPoint S)

/-! ### The three data of a one-point comparison, over an arbitrary ring -/

/-- **The three data of a `OnePointComparison`, stated over an arbitrary ring `A` and an
arbitrary right adjoint**, with the tensor comparison an *isomorphism*. -/
structure PointPresentation (S : RingedSpace.{u, u}) (A : CommRingCat.{u})
    (sections : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A)) where
  /-- The left adjoint `L : D(A) ⥤ D(𝒪_S)`. -/
  pullback : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))
  /-- `L` is left adjoint to the given model of derived global sections. -/
  adjunction : pullback ⊣ sections
  /-- The comparison `L(x ⊗^𝐋_A y) ≅ L x ⊗^𝐋_{𝒪_S} L y`, as an isomorphism of bifunctors. -/
  tensorIso : Functor.uncurry.obj
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A) ⋙ pullback ≅
      pullback.prod pullback ⋙ Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)

/-- A presentation over `Γ(S, 𝒪_S)` whose right adjoint is derived global sections *is* a
one-point comparison. -/
def PointPresentation.toComparison {A : CommRingCat.{u}}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A)}
    (d : PointPresentation S A G) (h : A = baseRing S)
    (e : transportFunctor h G ≅ baseSections S) : OnePointComparison S := by
  subst h
  exact
    { pullback := d.pullback
      adjunction := d.adjunction.ofNatIsoRight e
      tensorComparison := d.tensorIso.hom }

/-- The tensor comparison of `PointPresentation.toComparison` is invertible. -/
instance PointPresentation.isIso_toComparison_tensorComparison {A : CommRingCat.{u}}
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} A)}
    (d : PointPresentation S A G) (h : A = baseRing S)
    (e : transportFunctor h G ≅ baseSections S) :
    IsIso (d.toComparison S h e).tensorComparison := by
  subst h; exact inferInstanceAs (IsIso d.tensorIso.hom)

/-! ### The presentation attached to the morphism to the coefficient point -/

/-- The left adjoint of the canonical presentation: the one-point identification
`Mod(A) ≌ Mod(𝒪_{({*}, A)})` on derived categories, followed by the derived pullback along
`π`. -/
abbrev canonicalPullback :
    DerivedCategory (ModuleCat.{u} (baseRing (onePointRingedSpace ↥(baseRing S)))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) :=
  (onePointSectionsEquivalence ↥(baseRing S)).functor.mapDerivedCategory ⋙
    derivedPullback (toCoeffPoint S)

/-- **The canonical presentation**, over the coefficient point's own ring of global functions:
`Lπ^*` read on `D(A)`, the composite of the one-point adjunction with `Lπ^* ⊣ Rπ_*` of
Stacks 079W, and the one-point comparison of derived tensor products followed by the derived
pullback–tensor comparison of Stacks 079U. -/
def canonicalPointPresentation :
    PointPresentation S (baseRing (onePointRingedSpace ↥(baseRing S)))
      (derivedPushforward (toCoeffPoint S) ⋙ baseSections (onePointRingedSpace ↥(baseRing S))) where
  pullback := canonicalPullback S
  adjunction :=
    (onePointDerivedAdjunction ↥(baseRing S)).comp (derivedAdjunction (toCoeffPoint S))
  tensorIso :=
    Functor.isoWhiskerRight (onePointDerivedTensorIso ↥(baseRing S))
        (derivedPullback (toCoeffPoint S)) ≪≫
      Functor.isoWhiskerLeft
        (((onePointSectionsEquivalence ↥(baseRing S)).functor.mapDerivedCategory).prod
          ((onePointSectionsEquivalence ↥(baseRing S)).functor.mapDerivedCategory))
        (derivedPullbackTensorIso (toCoeffPoint S))

/-! ### Derived global sections through the coefficient point -/

/-- **Derived sections over `π⁻¹ ⊤ = ⊤` are derived global sections on `S`**, with scalars
restricted along `π^♯`. -/
def derivedPreimageSectionsIso :
    baseSections S ⋙ (coeffRestrict S).mapDerivedCategory ≅
      derivedPreimageSections (toCoeffPoint S) ⊤ :=
  totalRightDerivedMapDerivedCategoryIso (sectionsOverOpen S ⊤) (coeffRestrict S)

/-- **The right adjoint of the canonical presentation is derived global sections on `S`**, after
transport along the equality `baseRing_coeffPoint S` of the two rings: the Leray isomorphism of
Stacks 0D5W followed by `derivedPreimageSectionsIso`. -/
def canonicalSectionsIso :
    transportFunctor (baseRing_coeffPoint S)
        (derivedPushforward (toCoeffPoint S) ⋙ baseSections (onePointRingedSpace ↥(baseRing S))) ≅
      baseSections S :=
  transportIso (baseRing_coeffPoint S)
      (lerayIso (toCoeffPoint S) ≪≫ (derivedPreimageSectionsIso S).symm) ≪≫
    transportCompIsoId (baseRing_coeffPoint S) ((coeffRestrict S).mapDerivedCategory)
      (transportRestrictScalarsIsoId (baseRing_coeffPoint S) (coeffStructMap S)
        (heq_coeffStructMap S))
      (baseSections S)

/-! ### The canonical one-point comparison -/

/-- **The canonical one-point comparison on an arbitrary ringed space.**  It is the datum of
Cohomology, Section 0FKU attached to the morphism `π : S ⟶ ({*}, Γ(S, 𝒪_S))`: the derived
pullback `Lπ^*` read on `D(A)` through the one-point identification, its adjunction with `Rπ_*`
composed with the Leray isomorphism of Stacks 0D5W, and the derived pullback–tensor comparison of
Stacks 079U composed with the one-point comparison of derived tensor products. -/
def canonicalOnePointComparison : OnePointComparison S :=
  (canonicalPointPresentation S).toComparison S (baseRing_coeffPoint S) (canonicalSectionsIso S)

/-- **The tensor comparison of the canonical one-point comparison is invertible.** -/
instance isIso_canonicalOnePointComparison_tensorComparison :
    IsIso (canonicalOnePointComparison S).tensorComparison :=
  PointPresentation.isIso_toComparison_tensorComparison S _ _ _

/-- **The tensor comparison of the canonical one-point comparison is not the zero morphism of
bifunctors**, on any ringed space whose derived global sections do not vanish identically. -/
theorem canonicalOnePointComparison_tensorComparison_ne_zero
    (hS : ¬ ∀ U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      IsZero ((baseSections S).obj U)) :
    (canonicalOnePointComparison S).tensorComparison ≠ 0 := by
  intro hzero
  refine hS fun U => ?_
  set c := canonicalOnePointComparison S with hc
  set X := ((baseSections S).obj U,
    (DerivedCategory.singleFunctor (ModuleCat.{u} (baseRing S)) 0).obj
      (ModuleCat.of ↥(baseRing S) ↥(baseRing S)))
  have hzsrc : IsZero ((Functor.uncurry.obj (tensorBase S) ⋙ c.pullback).obj X) :=
    IsZero.of_mono_eq_zero (c.tensorComparison.app X) (by rw [hzero]; exact NatTrans.app_zero _)
  have hzL : IsZero (c.pullback.obj ((baseSections S).obj U)) :=
    hzsrc.of_iso (c.pullback.mapIso
      (CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso
        ((baseSections S).obj U)).symm)
  rw [IsZero.iff_id_eq_zero]
  exact (c.adjunction.homEquiv ((baseSections S).obj U) U).symm.injective
    (hzL.eq_of_src _ _)

end Stacks.Cohomology.DerivedGlobalCupProduct

end
