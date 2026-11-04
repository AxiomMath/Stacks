module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayRestrictionHomotopySquare

/-!
# The unit-free Leray restriction square

Let `f : X ⟶ Y` be a morphism of ringed spaces and `V' ≤ V` opens of `Y`. The identification
`Γ(V, f_* -) = Γ(f⁻¹ V, -)` of `pushforwardPreimageSectionsIso`, followed by the termwise
restriction of sections over `V`, is the termwise restriction of sections over `f⁻¹ V` followed by
the same identification over `V'`, read through restriction of scalars. Consequently the Leray
comparison `lerayComparison` and the Leray isomorphism `derivedSectionsPushforwardIso` are natural
in the open, one half of the restriction compatibility in [Stacks, Tag 0D68].

All names are in the namespace `Stacks.Cohomology.DerivedSectionsLeray`.

## Main results

* `preimageSectionsRestrict_eq`: restriction of sections over an inverse image is restriction of
  sections of a direct image.
* `lerayHomotopySquare`: the unit-free square on the homotopy category.
* `lerayComparison_comp_derivedSectionsOverOpenRestrict`: the transformation form of the Leray
  restriction square.
* `derivedSectionsPushforwardIso_restrict`: the object-wise form.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.HypercohomologyEdge (sectionsRestrict homotopySectionsRestrict)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

/-! ### A diagram lemma -/

/-- Two paths out of `F₀ ⋙ Q` agree: the image under `Q` of `a1 ≫ a2 ≫ a3` followed by `e`, and
the image of `b1 ≫ b2` followed by `n1 ≫ n2`, given the square `hab` and the step `hn`. -/
private theorem square_chain {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : D ⥤ E) {F₀ F₁ F₂ F₃ G₁ G₂ : C ⥤ D} {M T : C ⥤ E}
    {a1 : F₀ ⟶ F₁} {a2 : F₁ ⟶ F₂} {a3 : F₂ ⟶ F₃}
    {b1 : F₀ ⟶ G₁} {b2 : G₁ ⟶ G₂} {b3 : G₂ ⟶ F₃}
    {e : F₃ ⋙ Q ⟶ T} {n1 : G₂ ⋙ Q ⟶ M} {n2 : M ⟶ T}
    (hn : n1 ≫ n2 = Functor.whiskerRight b3 Q ≫ e)
    (hab : a1 ≫ a2 ≫ a3 = b1 ≫ b2 ≫ b3) :
    Functor.whiskerRight a1 Q ≫ Functor.whiskerRight a2 Q ≫ Functor.whiskerRight a3 Q ≫ e =
      (Functor.whiskerRight b1 Q ≫ Functor.whiskerRight b2 Q ≫ n1) ≫ n2 := by
  have := congrArg (fun t => Functor.whiskerRight t Q ≫ e) hab
  simpa [← hn] using this

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The termwise square -/

/-- **Restriction of sections over an inverse image is restriction of sections of a direct
image.**  Under the identification `Γ(V, f_* -) = Γ(f⁻¹ V, -)` of
`Stacks.Cohomology.DerivedSectionsLeray.pushforwardPreimageSectionsIso`, the restriction map
`Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrict` is the restriction map
`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict` of the sheaf of modules `f_* -` on `Y`. -/
theorem preimageSectionsRestrict_eq {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    preimageSectionsRestrict f hV =
      Functor.whiskerLeft (modulePushforward f) (sectionsRestrict (structureSheafRing Y) hV.hom) :=
  rfl

/-- **The termwise square on the homotopy category.**  `preimageSectionsRestrict_eq` read on
complexes: the identification at `V`, the termwise restriction of sections over `V` of a direct
image and the comparison of the two spellings of `Γ(V', -) ⋙ Res_ρ` compose to the termwise
restriction over the inverse image, the corresponding comparison, and the identification at `V'`
read through restriction of scalars. -/
theorem homotopyTermwise_eq {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    (Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
          (ComplexShape.up ℤ)).inv ≫
        Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (NatTrans.mapHomotopyCategory (sectionsRestrict (structureSheafRing Y) hV.hom)
            (ComplexShape.up ℤ)) ≫
        Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (sectionsOverOpen Y V' ⋙
              ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom))
            (ComplexShape.up ℤ)).inv =
      NatTrans.mapHomotopyCategory (preimageSectionsRestrict f hV) (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (preimageSections f V' ⋙
            ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom))
          (ComplexShape.up ℤ)).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv
          ((ModuleCat.restrictScalars
            ((structureSheafRing Y).obj.map hV.hom.op).hom).mapHomotopyCategory
            (ComplexShape.up ℤ)) :=
  rfl

/-! ### The naturality step -/

/-- **The comparison of restriction of scalars passes the identification at `V'`.**  This is the
naturality of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of
`CategoryTheory.ModuleCat.restrictScalars` along the components of
`Stacks.Cohomology.DerivedSectionsLeray.pushforwardPreimageSectionsIso` at `V'`. -/
theorem mapDerivedCategoryFactorsh_naturality_pushforwardPreimageSectionsIso
    {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    Functor.whiskerLeft ((preimageSections f V').mapHomotopyCategory (ComplexShape.up ℤ))
          (ModuleCat.restrictScalars
            ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactorsh.inv ≫
        Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
          (restrictScalarsDerived Y hV) =
      Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv
          ((ModuleCat.restrictScalars
            ((structureSheafRing Y).obj.map hV.hom.op).hom).mapHomotopyCategory
              (ComplexShape.up ℤ)))
          DerivedCategory.Qh ≫
        Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (Functor.whiskerLeft ((sectionsOverOpen Y V').mapHomotopyCategory (ComplexShape.up ℤ))
            (ModuleCat.restrictScalars
              ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactorsh.inv) :=
  NatTrans.ext <| funext fun _ ↦ (((ModuleCat.restrictScalars
    ((structureSheafRing Y).obj.map hV.hom.op).hom).mapDerivedCategoryFactorsh.inv).naturality
      _).symm

/-! ### The unit-free square -/

/-- **The unit-free Leray restriction square.**  The identification `Γ(V, f_* -) = Γ(f⁻¹ V, -)`
followed by the termwise restriction of sections over `V` is the termwise restriction of sections
over `f⁻¹ V` followed by the identification at `V'`, read through restriction of scalars. -/
theorem lerayHomotopySquare {V V' : Opens Y.carrier} (hV : V' ≤ V) :
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
          (pushforwardPreimageSectionsIso f V) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
        Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
          (homotopySectionsRestrict (structureSheafRing Y) hV.hom) =
      homotopyPreimageSectionsRestrict f hV ≫
        Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
            (pushforwardPreimageSectionsIso f V') (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
          (restrictScalarsDerived Y hV) :=
  square_chain DerivedCategory.Qh
    (mapDerivedCategoryFactorsh_naturality_pushforwardPreimageSectionsIso f hV)
    (homotopyTermwise_eq f hV)

/-! ### The Leray restriction square -/

/-- **The Leray restriction square, in transformation form.**  The naturality in the open of the
Leray comparison `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`. -/
theorem lerayComparison_comp_derivedSectionsOverOpenRestrict {V V' : Opens Y.carrier}
    (hV : V' ≤ V) :
    lerayComparison f V ≫
        Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV) =
      derivedPreimageSectionsRestrict f hV ≫
        Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV) :=
  lerayComparison_comp_derivedSectionsOverOpenRestrict_of_homotopySquare f hV
    (lerayHomotopySquare f hV)

/-- **The object-wise Leray restriction square.**  Restricting from `V` to `V'` after the Leray
isomorphism `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` at `V` is that
isomorphism at `V'` after the restriction on derived sections over the inverse image. This is one
half of the restriction compatibility in [Stacks, Tag 0D68]. -/
theorem derivedSectionsPushforwardIso_restrict {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSectionsOverOpenRestrict Y hV).app ((derivedPushforward f).obj K) ≫
        (restrictScalarsDerived Y hV).map ((derivedSectionsPushforwardIso f V').hom.app K) =
      (derivedSectionsPushforwardIso f V).hom.app K ≫
        (derivedPreimageSectionsRestrict f hV).app K :=
  derivedSectionsPushforwardIso_restrict_of_homotopySquare f hV (lerayHomotopySquare f hV) K

end Stacks.Cohomology.DerivedSectionsLeray

end
