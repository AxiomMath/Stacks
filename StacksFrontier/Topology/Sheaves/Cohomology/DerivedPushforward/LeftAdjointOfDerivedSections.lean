module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOnAPoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# Derived global sections on a ringed space have a left adjoint

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`.  This file constructs, with no hypothesis
on `S`, a left adjoint of derived global sections

`RΓ(S, -) : D(𝒪_S) ⥤ D(A)`.

The left adjoint is the one the source of Cohomology, Section 0FKU has in mind: `S` maps to the
one-point ringed space `({*}, A)` by the morphism `π` of Stacks 01BH attached to the identity of
`A`, modules on that point are `A`-modules, and the left adjoint is `Lπ^*` read through that
identification.  Concretely it is the composite

`D(A) ⥤ D(𝒪_{({*}, A)}) ⥤ D(𝒪_S)`

of the one-point identification on derived categories with the derived pullback `Lπ^*` of Tag
079W; that it is left adjoint to `RΓ(S, -)` is the adjunction of Tag 079W composed with the
adjunction of the one-point identification, read through the Leray isomorphism of Tag 0D5W at
the morphism `π` and the open `⊤`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePoint` — the one-point ringed space
  `({*}, Γ(S, 𝒪_S))` attached to `S`.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.toBasePoint` — the structure morphism
  `π : S ⟶ ({*}, Γ(S, 𝒪_S))` of Stacks 01BH, for the identity ring map.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRingEquiv` — `π^♯` on the whole space
  is an isomorphism of rings `Γ({*}, 𝒪) ≅ Γ(S, 𝒪_S)`.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRestrict` — the induced equivalence
  `Mod(Γ(S, 𝒪_S)) ≌ Mod(Γ({*}, 𝒪))`, whose functor *is* the restriction of scalars occurring in
  `Stacks.Cohomology.DerivedSectionsLeray.preimageSections π ⊤`.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.basePointRestrictAdjunction` — that equivalence
  on derived categories, as an adjunction.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.baseSectionsUnit` — the canonical comparison
  from termwise global sections to `RΓ(π⁻¹⊤, -)` with the scalars put back.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseExtension` — **the left adjoint**
  `D(A) ⥤ D(𝒪_S)`.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseAdjunction` — **the adjunction**
  `derivedBaseExtension S ⊣ RΓ(S, -)`, for an arbitrary ringed space `S`.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.preimageSections_eq` — sections over `π⁻¹⊤` with
  scalars restricted along `π^♯` *are* global sections followed by `basePointRestrict`; this
  holds by `rfl`, because `π⁻¹⊤ = ⊤` on the nose and `basePointRingEquiv` is built from `π^♯`
  itself rather than from an abstract inverse.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.isIso_baseSectionsUnit_app` — a K-injective
  complex computes both sides of that comparison.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.isIso_baseSectionsComparison` — consequently
  `RΓ(S, -)` and `RΓ(π⁻¹⊤, -)` agree after restriction of scalars: both are right derived
  functors of the same functor, with the same unit.

## Implementation notes

*Nothing is assumed.*  The three inputs are all unconditional in this repository:
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction` (Tag 079W) holds for every
morphism of ringed spaces, `Stacks.Cohomology.DerivedSectionsLeray.lerayIso` (Tag 0D5W) holds for
every morphism and every open, and `Stacks.AssociatedSheaf.onePointEquivalence` is a genuine
equivalence of abelian categories — built from the adjunction of Stacks 01BH by showing its unit
and counit invertible, not from essential surjectivity and `Classical.choice` — which
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedAdjunction` already promotes to derived
categories.

*The two spellings of the ring of global sections.* `Stacks.Cohomology.GlobalKunneth.baseRing S` is
`S.presheaf.obj (op ⊤)`, an object of `CommRingCat`, while sections of a sheaf of modules are taken
over `(structureSheafRing S).obj.obj (op ⊤)`, its image in `RingCat`. The two carriers are equal
only after unfolding `forget₂ CommRingCat RingCat`, which is *not* a reducible unfolding, so an
instance stated for one spelling is invisible to a goal written in the other: in particular
`(baseSections S).IsRightDerivedFunctor (derivedSectionsOverOpenUnit S ⊤) _` fails to synthesize
while the same goal written with `derivedSectionsOverOpen S ⊤` succeeds. Every declaration below
whose elaboration needs an instance is therefore written in the `structureSheafRing` spelling, and
only the final adjunction is stated with `baseSections S`, where the ascription is checked at
default transparency.

*Why `basePointRingEquiv` is built by hand.*  It would be shorter to take
`Stacks.AssociatedSheaf.coefficientRingEquiv` and invert it, but then the restriction of scalars
along `π^♯` — which is what `preimageSections π ⊤` contains — would agree with the functor of the
equivalence only propositionally, and `preimageSections_eq` would carry an `eqToHom`.  Taking
`π^♯` itself as the forward map of the equivalence, with `coefficientRingEquiv` as its inverse,
makes that equation `rfl` and keeps every later statement free of transport.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.DerivedSectionsLeftAdjoint

attribute [local instance] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u})

/-! ### The coefficient point of a ringed space -/

/-- **The coefficient point of `S`**: the one-point ringed space whose ring is
`A = Γ(S, 𝒪_S)`. -/
abbrev basePoint : RingedSpace.{u, u} := onePointRingedSpace.{u} (baseRing S)

/-- **The structure morphism `π : S ⟶ ({*}, Γ(S, 𝒪_S))`**, the morphism of ringed spaces of
construction (1) of Stacks 01BH attached to the identity ring map of `Γ(S, 𝒪_S)`. -/
abbrev toBasePoint : S ⟶ basePoint S := toCoefficientPoint' S (RingHom.id ↥(baseRing S))

/-- The component of `π^♯` on the whole space, a ring map `Γ({*}, 𝒪) ⟶ Γ(S, 𝒪_S)`. -/
abbrev basePointScalars :
    ((structureSheafRing (basePoint S)).obj.obj (op ⊤)) ⟶ ((structureSheafRing S).obj.obj (op ⊤)) :=
  pointStructureMap S (RingHom.id ↥(baseRing S))

/-- `π^♯` on the whole space undoes the identification of `Γ(S, 𝒪_S)` with the sections of the
coefficient point's structure sheaf.  This is `Stacks.AssociatedSheaf.structureSheafHom_app_top`
at the identity ring map. -/
theorem basePointScalars_coefficientRingEquiv (y : ↥(baseRing S)) :
    (basePointScalars S).hom ((coefficientRingEquiv (R := ↥(baseRing S))) y) = y :=
  structureSheafHom_app_top_apply S (RingHom.id ↥(baseRing S)) y

/-- **`π^♯` on the whole space is an isomorphism of rings** `Γ({*}, 𝒪) ≅ Γ(S, 𝒪_S)`, with
`Stacks.AssociatedSheaf.coefficientRingEquiv` as its inverse.  Its forward map is `π^♯` on the
nose, which is what makes `preimageSections_eq` hold by `rfl`. -/
def basePointRingEquiv :
    ↥((structureSheafRing (basePoint S)).obj.obj (op ⊤)) ≃+*
      ↥((structureSheafRing S).obj.obj (op ⊤)) :=
  { (basePointScalars S).hom with
    invFun := coefficientRingEquiv (R := ↥(baseRing S))
    left_inv := fun x => by
      have h := basePointScalars_coefficientRingEquiv S
        ((coefficientRingEquiv (R := ↥(baseRing S))).symm x)
      rw [RingEquiv.apply_symm_apply] at h
      change (coefficientRingEquiv (R := ↥(baseRing S))) ((basePointScalars S).hom x) = x
      rw [h, RingEquiv.apply_symm_apply]
    right_inv := basePointScalars_coefficientRingEquiv S }

/-- **Restriction of scalars along `π^♯` is an equivalence**
`Mod(Γ(S, 𝒪_S)) ≌ Mod(Γ({*}, 𝒪))`. -/
abbrev basePointRestrict :
    ModuleCat.{u} ↥((structureSheafRing S).obj.obj (op ⊤)) ≌
      ModuleCat.{u} ↥((structureSheafRing (basePoint S)).obj.obj (op ⊤)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (basePointRingEquiv S)

/-- **Sections over `π⁻¹⊤` are global sections, restricted along `π^♯`** — on the nose:
`π⁻¹⊤ = ⊤` by `rfl` on the one-point space, and the functor of `basePointRestrict` is
restriction of scalars along `π^♯` itself. -/
theorem preimageSections_eq :
    preimageSections (toBasePoint S) ⊤ = sectionsOverOpen S ⊤ ⋙ (basePointRestrict S).functor :=
  rfl

/-- Restriction of scalars along the inverse of `π^♯` is additive. -/
instance basePointRestrict_inverse_additive : (basePointRestrict S).inverse.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars
    ((basePointRingEquiv S).symm : ↥((structureSheafRing S).obj.obj (op ⊤)) →+*
      ↥((structureSheafRing (basePoint S)).obj.obj (op ⊤)))).Additive

/-! ### The restriction equivalence on derived categories -/

/-- The functor of `basePointRestrict` on cochain complexes and its derived functor commute with
the localization functors `DerivedCategory.Q`. -/
instance catCommSq_basePointRestrict_functor :
    CatCommSq ((basePointRestrict S).mapHomologicalComplex (ComplexShape.up ℤ)).functor
      DerivedCategory.Q DerivedCategory.Q (basePointRestrict S).functor.mapDerivedCategory :=
  ⟨((basePointRestrict S).functor.mapDerivedCategoryFactors).symm⟩

/-- The inverse of `basePointRestrict` on cochain complexes and its derived functor commute with
the localization functors `DerivedCategory.Q`. -/
instance catCommSq_basePointRestrict_inverse :
    CatCommSq ((basePointRestrict S).mapHomologicalComplex (ComplexShape.up ℤ)).inverse
      DerivedCategory.Q DerivedCategory.Q (basePointRestrict S).inverse.mapDerivedCategory :=
  ⟨((basePointRestrict S).inverse.mapDerivedCategoryFactors).symm⟩

/-- **The restriction equivalence on derived categories, as an adjunction.**  Both functors are
exact, so the adjunction of the abelian equivalence descends along the localizations `Q`. -/
def basePointRestrictAdjunction :
    (basePointRestrict S).functor.mapDerivedCategory ⊣
      (basePointRestrict S).inverse.mapDerivedCategory :=
  Adjunction.localization
    ((basePointRestrict S).mapHomologicalComplex (ComplexShape.up ℤ)).toAdjunction
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} ↥((structureSheafRing S).obj.obj (op ⊤)))
      (ComplexShape.up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (ModuleCat.{u} ↥((structureSheafRing (basePoint S)).obj.obj (op ⊤)))
      (ComplexShape.up ℤ))
    _ _

/-! ### Derived sections over `π⁻¹⊤`, with the scalars put back, are derived global sections -/

/-- Sections over `π⁻¹⊤` with the scalars first restricted along `π^♯` and then put back are
global sections. -/
def preimageRestrictIso :
    preimageSections (toBasePoint S) ⊤ ⋙ (basePointRestrict S).inverse ≅ sectionsOverOpen S ⊤ :=
  Functor.isoWhiskerLeft (sectionsOverOpen S ⊤) (basePointRestrict S).unitIso.symm ≪≫
    (sectionsOverOpen S ⊤).rightUnitor

/-- `preimageRestrictIso` on the homotopy categories of cochain complexes. -/
def homotopyPreimageRestrictIso :
    (preimageSections (toBasePoint S) ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (basePointRestrict S).inverse.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (sectionsOverOpen S ⊤).mapHomotopyCategory (ComplexShape.up ℤ) :=
  @Functor.mapHomotopyCategoryCompIso ℤ _ _ _ _ _ _ _ _ _ _ _ _ (preimageRestrictIso S) _
    (basePointRestrict_inverse_additive S) (sectionsOverOpen_additive S ⊤) (ComplexShape.up ℤ)

/-- `preimageRestrictIso` read on the homotopy category with values in the derived category:
termwise sections over `π⁻¹⊤`, with the scalars put back, are termwise global sections. -/
def derivedPreimageRestrictIso :
    homotopyPreimageSections (toBasePoint S) ⊤ ⋙
        (basePointRestrict S).inverse.mapDerivedCategory ≅
      homotopySectionsOverOpen S ⊤ :=
  Functor.isoWhiskerLeft
      ((preimageSections (toBasePoint S) ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      ((basePointRestrict S).inverse.mapDerivedCategoryFactorsh) ≪≫
    Functor.isoWhiskerRight (homotopyPreimageRestrictIso S) DerivedCategory.Qh

/-- The canonical comparison from termwise global sections to `RΓ(π⁻¹⊤, -)` with the scalars put
back: the identification `Γ(S, -) = Γ(π⁻¹⊤, -)` of `derivedPreimageRestrictIso`, followed by the
unit of `RΓ(π⁻¹⊤, -)`. -/
def baseSectionsUnit :
    homotopySectionsOverOpen S ⊤ ⟶
      DerivedCategory.Qh ⋙
        (derivedPreimageSections (toBasePoint S) ⊤ ⋙
          (basePointRestrict S).inverse.mapDerivedCategory) :=
  (derivedPreimageRestrictIso S).inv ≫
    Functor.whiskerRight (derivedPreimageSectionsUnit (toBasePoint S) ⊤)
      (basePointRestrict S).inverse.mapDerivedCategory

/-- **A K-injective complex computes the comparison.**  Its first factor is a component of an
isomorphism and its second is the image of the unit of `RΓ(π⁻¹⊤, -)`, which a K-injective complex
computes by Tag 070K. -/
theorem isIso_baseSectionsUnit_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S)) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((baseSectionsUnit S).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S))
        (ComplexShape.up ℤ)).obj I)) := by
  have h₁ : IsIso ((derivedPreimageSectionsUnit (toBasePoint S) ⊤).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S))
        (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        u, u + 1, u + 1, u + 1, u + 1, u + 1}
      (homotopyPreimageSections (toBasePoint S) ⊤) (exists_quasiIso_isKInjective S)).2
      DerivedCategory.Qh _ (derivedPreimageSectionsUnit (toBasePoint S) ⊤) I hI
  change IsIso ((derivedPreimageRestrictIso S).inv.app _ ≫
    (basePointRestrict S).inverse.mapDerivedCategory.map _)
  infer_instance

/-- `RΓ(π⁻¹⊤, -)` with the scalars put back is a right derived functor of termwise global
sections, with unit `baseSectionsUnit`. -/
instance isRightDerivedFunctor_derivedPreimageSections_comp :
    (derivedPreimageSections (toBasePoint S) ⊤ ⋙
        (basePointRestrict S).inverse.mapDerivedCategory).IsRightDerivedFunctor
      (baseSectionsUnit S)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    _ (exists_quasiIso_isKInjective S) DerivedCategory.Qh _ (baseSectionsUnit S)
    (fun I hI => isIso_baseSectionsUnit_app S I hI)

/-- The comparison `RΓ(S, -) ⟶ RΓ(π⁻¹⊤, -)` with the scalars put back, induced by
`baseSectionsUnit` through the universal property of `RΓ(S, -)`. -/
def baseSectionsComparison :
    derivedSectionsOverOpen S ⊤ ⟶ derivedPreimageSections (toBasePoint S) ⊤ ⋙
      (basePointRestrict S).inverse.mapDerivedCategory :=
  (derivedSectionsOverOpen S ⊤).rightDerivedDesc (derivedSectionsOverOpenUnit S ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) _
    (baseSectionsUnit S)

/-- **Derived global sections on `S` are derived sections over `π⁻¹⊤`, with the scalars put
back.**  Both are right derived functors of termwise global sections with the same unit, so the
comparison between them is invertible. -/
instance isIso_baseSectionsComparison : IsIso (baseSectionsComparison S) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ (derivedSectionsOverOpenUnit S ⊤)
    _ _ (baseSectionsUnit S)).1 inferInstance

/-! ### The left adjoint -/

/-- The one-point identification on derived categories,
`D(Γ({*}, 𝒪)) ⥤ D(𝒪_{({*}, Γ(S, 𝒪_S))})`. -/
abbrev basePointExtension : DerivedCategory (ModuleCat.{u} (baseRing (basePoint S))) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (basePoint S))) :=
  (onePointSectionsEquivalence ↥(baseRing S)).functor.mapDerivedCategory

/-- **The left adjoint of derived global sections**, `D(Γ(S, 𝒪_S)) ⥤ D(𝒪_S)`: restriction of
scalars along `π^♯`, the one-point identification, and the derived pullback `Lπ^*` of Tag 079W.
On a module `M` placed in degree zero it is `L π^* M`, that is, the derived version of
`M ↦ M ⊗_A 𝒪_S`. -/
def derivedBaseExtension : DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) :=
  (basePointRestrict S).functor.mapDerivedCategory ⋙
    (basePointExtension S ⋙ derivedPullback (toBasePoint S))

/-- `Lπ^*` is left adjoint to `RΓ({*}, Rπ_*(-))`: the adjunction of Tag 079W composed with the
one-point identification's adjunction. -/
def basePointAdjunction : (basePointExtension S ⋙ derivedPullback (toBasePoint S)) ⊣
    (derivedPushforward (toBasePoint S) ⋙ baseSections (basePoint S)) :=
  Adjunction.comp (onePointDerivedAdjunction ↥(baseRing S)) (derivedAdjunction (toBasePoint S))

/-- The same adjunction with its right adjoint read through the Leray isomorphism of Tag 0D5W:
`RΓ({*}, Rπ_*(-))` is `RΓ(π⁻¹⊤, -)`. -/
def basePointAdjunctionLeray : (basePointExtension S ⋙ derivedPullback (toBasePoint S)) ⊣
    derivedPreimageSections (toBasePoint S) ⊤ :=
  Adjunction.ofNatIsoRight (basePointAdjunction S) (lerayIso (toBasePoint S))

/-- The same adjunction after restoring the scalars on the right-hand side. -/
def derivedBaseAdjunctionAux : derivedBaseExtension S ⊣
    (derivedPreimageSections (toBasePoint S) ⊤ ⋙
      (basePointRestrict S).inverse.mapDerivedCategory) :=
  Adjunction.comp (basePointRestrictAdjunction S) (basePointAdjunctionLeray S)

/-- **Derived global sections on an arbitrary ringed space have a left adjoint.**

`derivedBaseExtension S ⊣ RΓ(S, -) : D(𝒪_S) ⥤ D(Γ(S, 𝒪_S))`.

No hypothesis is imposed on `S`. -/
def derivedBaseAdjunction : derivedBaseExtension S ⊣ baseSections S :=
  Adjunction.ofNatIsoRight (derivedBaseAdjunctionAux S) (asIso (baseSectionsComparison S)).symm

end Stacks.Cohomology.DerivedSectionsLeftAdjoint

end
