module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor

/-!
# Derived sections over an object along a functor of sites that are not small

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and `g : Sh(C) ⟶ Sh(D)` the
corresponding morphism of topoi. **Stacks 0DD8 (1)** says that for an object `U` of `C` the
derived sections over `U` of an inverse image are the derived sections over `u(U)`:

`RΓ(U, g⁻¹K) = RΓ(u(U), K)` for `K` in the unbounded derived category of abelian sheaves on `D`.

That statement is already in this library as
`Stacks.Cohomology.DerivedLowerShriek.derivedAbelianSectionsRestrictionIso`, but only for *small*
sites with the coefficients in the one universe `u` of their objects and morphisms. The geometric
sites of the chapter on derived categories of stacks are not of that shape: the fppf site of an
algebraic stack and its flat-fppf and lisse-étale subsites have their objects one universe above
their morphisms, and their abelian sheaves take values one universe above the morphisms too. This
file restates the same chain at

`C, D : Type u₁` with `Category.{v}` and coefficients `AddCommGrpCat.{max u₁ v w}`,

which specializes to a small site at `u₁ = v = w` and to a geometric site at `u₁ = w = u + 1`,
`v = u`.

## What the universe constraint is, and why it is this one

The proof of Stacks 0DD8 (1) runs through corepresentability of sections over `U` by the free
abelian sheaf `j_{U!} ℤ_U` (Stacks 0G1V), and corepresentability is expressed with
`CategoryTheory.preadditiveCoyoneda`, whose coefficient universe is *the morphism universe of the
ambient category*. For `A = Sheaf J AddCommGrpCat.{t}` that morphism universe is `max u₁ t`, so
the corepresentation statement typechecks exactly when `u₁ ≤ t`. Smallness is one way to get
that; writing the coefficient universe as `max u₁ v w` is another, and it is the one the
geometric sites satisfy. Nothing in the chain needs `C` or `D` to be small, and nothing needs
`Small.{t} C`: Grothendieck abelianness of the two sheaf categories, which Mathlib's instance
supplies only for a small site, is carried here as an instance argument — it is available for a
geometric site from essential smallness through
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.abelianSections` and
  `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSections`: sections over an object
  of a site, and their unbounded right derived functor `RΓ(U, -)`.
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.abelianSectionsCorepresentation`: **Stacks 0G1V**
  as an isomorphism of additive functors, `Hom(j_{U!} ℤ_U, -) ≅ Γ(U, -)`.
* `Stacks.Cohomology.DerivedLowerShriek.BigSite.DerivedAbelianLowerShriekComputesGenerator`: the
  invertibility of the derived lower-shriek counit at the single complex of `j_{U!} ℤ_U`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSectionsRestrictionIso`:
  **Stacks 0DD8**, part (1), at these universes.

## Implementation notes

Every general lemma the original chain uses — the corepresentability criterion for a
right-derived unit, the transport of bijectivity along an adjunction, the recognition of a right
derived functor on K-injective complexes, and the whole of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` — is
already universe-polymorphic, so this file only restates the four declarations that were pinned
and reuses those unchanged. The two sites are kept in one object universe `u₁` and one morphism
universe `v` because the coefficient category has to be the same on both sides.

## References

* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

/-! ### Sections over an object of a site that is not small -/

section Sections

variable {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sections of an abelian sheaf over an object of a site, at coefficients in the join of the
object universe, the morphism universe and an arbitrary further universe. -/
abbrev abelianSections (U : C) :
    Sheaf J AddCommGrpCat.{max u₁ v w} ⥤ AddCommGrpCat.{max u₁ v w} :=
  (sheafSections J AddCommGrpCat.{max u₁ v w}).obj (op U)

/-- Sections of an abelian sheaf over an object form an additive functor. -/
instance additive_abelianSections (U : C) : (abelianSections.{w} J U).Additive where
  map_add := rfl

attribute [local instance] HasDerivedCategory.standard

/-- Sections over an object have an unbounded right derived functor, by the functorial
K-injective resolutions of Stacks 079P in the Grothendieck abelian category of abelian sheaves.
Grothendieck abelianness is an instance argument rather than found by search: Mathlib's instance
for a sheaf category covers only a small site. -/
instance hasRightDerivedFunctor_abelianSections (U : C)
    [HasSheafify J AddCommGrpCat.{max u₁ v w}]
    [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})] :
    ((abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)) :=
  alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- `RΓ(U, -)` on abelian sheaves: the unbounded right derived functor of sections over `U`. -/
abbrev derivedAbelianSections (U : C) [HasSheafify J AddCommGrpCat.{max u₁ v w}]
    [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})] :
    DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ v w}) ⥤
      DerivedCategory AddCommGrpCat.{max u₁ v w} :=
  ((abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))

/-- **Stacks 0G1V as an isomorphism of additive functors, on a site that is not small.**
Morphisms out of the free abelian sheaf `j_{U!} ℤ_U` are the sections over `U`.

The coefficient universe is forced to contain the object universe `u₁`: the left-hand side is
built with `CategoryTheory.preadditiveCoyoneda`, whose values live in the morphism universe of
the ambient category, which for abelian sheaves on `(C, J)` is `max u₁` the coefficient
universe. -/
def abelianSectionsCorepresentation (U : C) [HasSheafify J AddCommGrpCat.{max u₁ v w}] :
    preadditiveCoyoneda.obj (op (extensionByZeroUnitAb.{max u₁ v w} J U)) ≅
      abelianSections.{w} J U := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · exact (show (_ ≃+ (F.obj.obj (op U) : Type (max u₁ v w)) ) from
      { extensionByZeroUnitAbHomEquiv.{max u₁ v w} J U F with
        map_add' := by
          intro f g
          change extensionByZeroUnitAbHomEquiv.{max u₁ v w} J U F (f + g) =
            extensionByZeroUnitAbHomEquiv.{max u₁ v w} J U F f +
              extensionByZeroUnitAbHomEquiv.{max u₁ v w} J U F g
          rfl }).toAddCommGrpIso
  · intro F G g
    ext φ
    exact extensionByZeroUnitAbHomEquiv_naturality.{max u₁ v w} J φ g

end Sections

/-! ### Stacks 0DD8, part (1), on sites that are not small -/

section Abelian

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (U : C)

attribute [local instance] HasDerivedCategory.standard

omit [f.IsCocontinuous J K] in
/-- **`Γ(U, g⁻¹(-)) = Γ(u(U), -)`.** The underlying presheaf of a restriction is precomposition
with `uᵒᵖ`, so sections over `U` of a restricted abelian sheaf are sections over `u(U)`. -/
theorem abelianRestriction_comp_abelianSections :
    abelianRestriction.{max u₁ v w} J K f ⋙ abelianSections.{w} J U =
      abelianSections.{w} K (f.obj U) :=
  rfl

variable [HasSheafify J AddCommGrpCat.{max u₁ v w}] [HasSheafify K AddCommGrpCat.{max u₁ v w}]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v w} J K).IsRightAdjoint]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v w}, f.op.HasPointwiseRightKanExtension F]
  [(abelianLowerShriekOnHomotopy.{max u₁ v w} J K f ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian.{max u₁ v w} (Sheaf K AddCommGrpCat.{max u₁ v w})]
  [(derivedAbelianLowerShriek.{max u₁ v w} J K f ⋙
    derivedAbelianRestriction.{max u₁ v w} J K f).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{max u₁ v w} J K f)
      (derivedAbelianRestriction.{max u₁ v w} J K f)).inv ≫
      Functor.whiskerRight (derivedAbelianLowerShriekComparison.{max u₁ v w} J K f)
        (derivedAbelianRestriction.{max u₁ v w} J K f))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))]

/-- The invertibility of the derived lower-shriek counit at the single complex of the free
abelian sheaf `j_{U!} ℤ_U`. This is the half of Stacks 0794 saying that the left derived functor
is computed on the `P`-cellular complexes, at a single complex whose term lies in `P`; it is the
one input of Stacks 07AC not available as a declaration in this library, the resolving class of
the construction being private to
`StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean`. -/
abbrev DerivedAbelianLowerShriekComputesGenerator : Prop :=
  IsIso ((derivedAbelianLowerShriekComparison.{max u₁ v w} J K f).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj (extensionByZeroUnitAb.{max u₁ v w} J U))))

variable [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})]

/-- **The restriction of a K-injective complex of abelian sheaves computes derived sections over
an object.** Sections over `U` are corepresented by `j_{U!} ℤ_U`, and the derived adjunction of
Stacks 07AC turns morphisms out of that generator into morphisms out of its derived lower shriek
on the other site, where the complex is K-injective. -/
theorem abelianSections_restriction_rightDerivedUnit_isIso
    (hgen : DerivedAbelianLowerShriekComputesGenerator.{w} J K f U)
    (I : CochainComplex (Sheaf K AddCommGrpCat.{max u₁ v w}) ℤ) [I.IsKInjective]
    (RT : DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ v w}) ⥤
      DerivedCategory AddCommGrpCat.{max u₁ v w})
    (α : (abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))] :
    IsIso (α.app ((abelianRestrictionOnHomotopy.{max u₁ v w} J K f).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hgen' := hgen
  refine rightDerivedUnit_isIso_of_corepresentable (abelianSections.{w} J U)
    (extensionByZeroUnitAb.{max u₁ v w} J U) (abelianSectionsCorepresentation.{w} J U) RT α
    (((abelianRestriction.{max u₁ v w} J K f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (fun n => ?_)
  refine qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((abelianRestriction.{max u₁ v w} J K f).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).app I)) ?_
  exact map_bijective_of_adjunction_comparison (abelianHomotopyAdjunction.{max u₁ v w} J K f)
    DerivedCategory.Qh DerivedCategory.Qh
    (derivedAbelianLowerShriekAdjunction.{max u₁ v w} J K f)
    (derivedAbelianLowerShriekComparison.{max u₁ v w} J K f)
    (derivedAbelianRestrictionComparison.{max u₁ v w} J K f)
    (derivedAbelianLowerShriekAdjunction_unit_fac.{max u₁ v w} J K f) _ _
    (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))

/-- The unit exhibiting derived restriction followed by derived sections over `U` as a candidate
right derived functor of sections over `u(U)`. -/
def restrictedAbelianSectionsUnit :
    (abelianSections.{w} K (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedAbelianRestriction.{max u₁ v w} J K f ⋙
        derivedAbelianSections.{w} J U) :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
    (eqToIso (abelianRestriction_comp_abelianSections.{w} J K f U))
    (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (abelianRestrictionOnHomotopy.{max u₁ v w} J K f)
    (((abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (derivedAbelianRestrictionComparison.{max u₁ v w} J K f)
    (derivedAbelianSections.{w} J U) ≫
  (Functor.associator _ _ _).hom

/-- **Stacks 0DD8, part (1), on sites that need not be small.** Let `u : C ⥤ D` be a continuous
and cocontinuous functor of sites and let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of
topoi. For every object `U` of `C` and every `K` in the unbounded derived category of abelian
sheaves on `D`, `RΓ(U, g⁻¹K) = RΓ(u(U), K)`, naturally in `K`. -/
def derivedAbelianSectionsRestrictionIso
    (hgen : DerivedAbelianLowerShriekComputesGenerator.{w} J K f U) :
    derivedAbelianRestriction.{max u₁ v w} J K f ⋙ derivedAbelianSections.{w} J U ≅
      derivedAbelianSections.{w} K (f.obj U) := by
  have hβ : (derivedAbelianRestriction.{max u₁ v w} J K f ⋙
      derivedAbelianSections.{w} J U).IsRightDerivedFunctor
        (restrictedAbelianSectionsUnit.{w} J K f U)
        (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_kInjective _ _ _ (fun I hI => ?_)
    have := hI
    have := abelianSections_restriction_rightDerivedUnit_isIso.{w} J K f U hgen I _
      (((abelianSections.{w} J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)))
    dsimp only [restrictedAbelianSectionsUnit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact Functor.rightDerivedUnique _ _ (restrictedAbelianSectionsUnit.{w} J K f U)
    (((abelianSections.{w} K (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))

end Abelian

end Stacks.Cohomology.DerivedLowerShriek.BigSite

end
