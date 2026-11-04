module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalKoszulTowerDerivedSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerSections
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleDerivedLimitTriangle
public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison
public import StacksFrontier.Homology.DerivedComplete.CountableMilnorTower
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections of the quotient tower are the derived completion

Let `A` be a ring, let `f ∈ A`, let `X` be a scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let
`ℱ` be a quasi-coherent `𝒪_X`-module whose `f`-power torsion `ℱ[fⁿ] = Ker(fⁿ : ℱ → ℱ)`
stabilizes. The displayed equality of [Stacks, Tag 0BLD] is

`RΓ(X, lim ℱ/fⁿℱ) = RΓ(X, ℱ)^∧`,

the right-hand side being the derived `f`-adic completion of `RΓ(X, ℱ)` in `D(A)`. This file
proves it, in the form of an isomorphism in `D(A)`.

The argument is the one the source gives, read through the four results this library already
has. The ordinary limit `lim ℱ/f^(n+1)ℱ`, in degree zero, is a derived limit of the tower of
quotients, because the quotients are quasi-coherent and the transitions are surjective on affine
sections (Tag 0EI8, available here as
`PrincipalQuotientTower.isDerivedLimit_single_limit_Csys`). Stabilization makes the tower of
quotients pro-isomorphic to the `f`-power Koszul tower (Tag 0H3D), so a derived limit `Ehat` of
the Koszul tower is isomorphic to it. Derived sections over the base ring commute with derived
limits (Tag 0D60), so `RΓ(X, Ehat)` is a derived limit of the tower `n ↦ RΓ(X, ℱ ⊗ Kos(f^(n+1)))`.
That tower is the `f`-power Koszul tower of `RΓ(X, ℱ)` over `A` (Tag 0H3C, available here as
`KoszulTowerSections.nonempty_iso_koszulTower_derivedSections`), so that same object
is a derived limit of `n ↦ RΓ(X, ℱ) ⊗^L_A (A --f^(n+1)--> A)`. The derived completion of a
complex is, by Tag 0BKG, the mapping-cocone model of the Milnor limit of exactly that tower, and
that model is itself a derived limit of the tower, so the two agree by uniqueness of derived
limits (Tag 07KZ).

Derived completion is presented as in Tags 0BKG and 0H32: the statement is quantified over an
arbitrary left adjoint `completion` to the inclusion `P.ι` of the derived-complete objects, so
`(-)^∧` is `completion ⋙ P.ι` and no particular construction of it is privileged. Such data
exists, by `Stacks.FormalFunctions.derivedComplete_principal_ι_isRightAdjoint`.

## Main definitions

* `Stacks.Algebraization.PrincipalQuotientTowerCompletion.derivedSectionsModule` — the object
  `RΓ(X, ℱ)` of `D(A)`.

## Main results

* `Stacks.Algebraization.PrincipalQuotientTowerCompletion.isDerivedLimit_milnorTriangle_obj₁` —
  the mapping-cocone model of the Milnor limit of an inverse system of cochain complexes of
  `A`-modules is a derived limit of that system in `D(A)`. This is the general form of a fact
  that the library previously had only for systems of modules placed in degree zero, and only
  privately.
* `Stacks.Algebraization.PrincipalQuotientTowerCompletion`
  `.nonempty_iso_koszulTower_comp_derivedSections` — derived sections over `A` carry the
  `f`-power Koszul tower of `ℱ` on `X` to the `f`-power Koszul tower of `RΓ(X, ℱ)` over `A`,
  compatibly with the transition maps. This is the step that the source of [Stacks, Tag 0H3C]
  asserts with "details left out".
* `Stacks.Algebraization.PrincipalQuotientTowerCompletion`
  `.nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion` — the displayed equality
  of [Stacks, Tag 0BLD]: `RΓ(X, lim ℱ/f^(n+1)ℱ)` is isomorphic to the derived `f`-adic completion
  of `RΓ(X, ℱ)`; it is therefore itself derived complete for `(f)`, and its cohomology modules
  are the cohomology modules of `RΓ(X, ℱ)^∧`, which is the identification the diagram of the
  source rests on.

## Implementation notes

The comparison of the two `f`-power Koszul towers — the second of the two ingredients of the
proof of [Stacks, Tag 0H3C], the one the source states with "details left out" — is
`nonempty_iso_koszulTower_comp_derivedSections` here. It rests on
`Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections`, which proves
the levelwise identification
`RΓ(X, ℱ ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)) ≅ RΓ(X, ℱ) ⊗^L_A (A --f^(n+1)--> A)` compatibly with
the transition maps, for an arbitrary cochain complex of sheaves of `𝒪_X`-modules, and on
`Stacks.Cohomology.KoszulTowerSections.ksysIso`, which identifies the inverse system `Ksys` used
here with the `f`-power Koszul tower of `ℱ` placed in cohomological degree zero. Both of the
hypotheses the source uses — quasi-coherence of `ℱ` and stabilization of its `f`-power
torsion — are consumed in the proof here, the first through Tag 0EI8 and the second through the
pro-isomorphism of Tag 0H3D, so the improvement over [Bhatt-local, Lemma 1.6] that stabilization
buys is the hypothesis actually used and not a stronger one.

`isDerivedLimit_milnorTriangle_obj₁` is proved by observing that
`CompletionSequences.complexDifference` and `CountableMilnorTower.oneMinusShift` are the same
`Pi.lift`, so that the first vertex of `CompletionSequences.milnorTriangle` is the value of
`CountableMilnorTower.countableMilnorFunctor` and the distinguished Milnor triangle for it is
already available. Going instead through `piComparison` requires transporting the triangle across
an isomorphism whose two ends are identified only by unfolding `getLimitCone`, which is the step
the module version of this lemma needs a transparency option for.

The three `HasProduct` side conditions of the derived limits, and the countable products of
`D(A)`, are carried as instance binders, exactly as in the middle-column theorem and in
Tag 0BKG; they are not quietly strengthened.

## What is not done here

Only the displayed equality, and the two statements that follow from it at once, are covered.

* The middle column of the diagram — the short exact sequence
  `0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0` — is not proved here; it
  is carried by
  `PrincipalQuotientTower.exists_shortExact_homology_derivedSections_limit_quotientTower`.
* The remaining rows and columns of the diagram of the source are not proved here: the top row
  `0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, the middle row
  `0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, the left column, and the
  bottom isomorphism `R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`. All of them are the diagram
  of [Stacks, Tag 0H32] for `K = RΓ(X, ℱ)`, which this library has as
  `PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison`, transported along
  the isomorphism proved here; that transport is carried out in
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/PrincipalQuotientTowerDiagram.lean`.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0H3E](https://stacks.math.columbia.edu/tag/0H3E)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
* [Stacks Project, Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase
  (baseSmul derivedSectionsOver isDerivedLimit_map_derivedSectionsOver)
open Stacks.Cohomology.QuotientTowerFormalFunctions
  (nonempty_iso_isDerivedLimit_koszulTower_quotientTower)
open Stacks.Algebraization.PrincipalQuotientTower
  (mulF quotientTower isDerivedLimit_single_limit_Csys)

universe u

namespace Stacks.Algebraization.PrincipalQuotientTowerCompletion

attribute [local instance] HasDerivedCategory.standard

/-- **The mapping-cocone model of a Milnor limit is a derived limit.** For an inverse system `E`
of cochain complexes of `A`-modules, the first vertex of the Milnor triangle of `1 - shift` on
`∏ₙ Eₙ` — the mapping cocone of that difference — is a derived limit in `D(A)` of the system `E`
read in `D(A)`.

The difference `1 - shift` of `CompletionSequences` and the one of `CountableMilnorTower` are the
same `Pi.lift`, so the object in question is the value of `countableMilnorFunctor` and the
distinguished Milnor triangle for it is the one already proved there. -/
theorem isDerivedLimit_milnorTriangle_obj₁ (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) :
    IsDerivedLimit (E ⋙ DerivedCategory.Q)
      ((CompletionSequences.milnorTriangle A E).obj₁) := by
  obtain ⟨δ, hδ⟩ := CountableMilnorTower.map_quasiIso_and_milnor_triangle.2 E
  exact ⟨_, δ, hδ⟩

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.toRingedSpace.carrier)))
  (f : A) (ℱ : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- **`RΓ(X, ℱ)` over the base ring.** The derived sections over `A` of the sheaf of
`𝒪_X`-modules `ℱ`, placed in cohomological degree zero. -/
abbrev derivedSectionsModule : DerivedCategory (ModuleCat.{u} A) :=
  (derivedSectionsOver X.toRingedSpace ρ).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj ℱ)

/-- **The step that the source of [Stacks, Tag 0H3C] omits.** Derived sections over the base ring
carry the `f`-power Koszul tower `n ↦ ℱ ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` of `ℱ` on `X` to the
`f`-power Koszul tower `n ↦ RΓ(X, ℱ) ⊗^L_A (A --f^(n+1)--> A)` of `RΓ(X, ℱ)` over `A`, compatibly
with the transition maps.

The proof of [Stacks, Tag 0H3C] asserts this with "details left out". It is
`Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections` at the complex
`ℱ` placed in cohomological degree zero, read through
`Stacks.Cohomology.KoszulTowerSections.ksysIso`, which identifies the inverse system `Ksys` of
cones of the iterated multiplication by `f` with the `f`-power Koszul tower of that complex. -/
theorem nonempty_iso_koszulTower_comp_derivedSections :
    Nonempty (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ ≅
      PrincipalTorsionTower.principalDerivedTensorSystem A f (derivedSectionsModule X ρ ℱ)) := by
  obtain ⟨e⟩ := Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections
    X.toRingedSpace ρ f (sgl.obj ℱ)
  exact ⟨Functor.isoWhiskerRight
      (Stacks.Cohomology.KoszulTowerSections.ksysIso X.toRingedSpace
        (baseSmul X.toRingedSpace ρ f) ℱ) (derivedSectionsOver X.toRingedSpace ρ) ≪≫
    Functor.associator _ _ _ ≪≫ e⟩

/-- **Formal sections for a principal ideal: the displayed equality of [Stacks, Tag 0BLD].** Let
`A` be a ring, `f ∈ A`, let `X` be a scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let `ℱ` be a
quasi-coherent `𝒪_X`-module whose `f`-power torsion stabilizes. Let `completion` be a left
adjoint to the inclusion of the objects of `D(A)` that are derived complete for the ideal `(f)`,
so that `(-)^∧ = completion ⋙ P.ι` is derived `f`-adic completion as in [Stacks, Tag 0BKG].
Then

`RΓ(X, lim ℱ/f^(n+1)ℱ) ≅ RΓ(X, ℱ)^∧`,

the object `RΓ(X, lim ℱ/f^(n+1)ℱ)` is itself derived complete for `(f)`, and for every `p` its
`p`-th cohomology module is that of `RΓ(X, ℱ)^∧` — the identification
`Hᵖ(X, lim ℱ/fⁿℱ) = Hᵖ(RΓ(X, ℱ)^∧)` on which the diagram of the source rests.

The levelwise comparison of the two `f`-power Koszul towers, which the source of
[Stacks, Tag 0H3C] asserts with details omitted, is
`nonempty_iso_koszulTower_comp_derivedSections`. -/
@[stacks 0BLD "the displayed equality `RΓ(X, lim ℱ/fⁿℱ) = RΓ(X, ℱ)^∧`, with derived f-adic \
completion presented as in Stacks 0BKG by an arbitrary left adjoint to the inclusion of the \
derived-complete objects; also derived completeness of `RΓ(X, lim ℱ/fⁿℱ)` and the identification \
`Hᵖ(X, lim ℱ/fⁿℱ) = Hᵖ(RΓ(X, ℱ)^∧)`. Unconditional. The levelwise identification \
`RΓ(X, ℱ ⊗_{𝒪_X} (𝒪_X --fⁿ--> 𝒪_X)) ≅ RΓ(X, ℱ) ⊗^L_A (A --fⁿ--> A)` of inverse systems, which \
the source's proof of Stacks 0H3C asserts with details left out, is proved here as \
`nonempty_iso_koszulTower_comp_derivedSections`, out of \
`Stacks.Cohomology.KoszulTowerSections.nonempty_iso_koszulTower_derivedSections`. The middle \
column of the diagram is carried by \
`PrincipalQuotientTower.exists_shortExact_homology_derivedSections_limit_quotientTower`; the \
remaining rows and columns of the diagram are not covered"]
theorem nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion
    (hℱ : (ℱ : X.Modules).IsQuasicoherent) (hstab : Stabilizes (mulF X ρ f ℱ))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let Fhat : DerivedCategory (ModuleCat.{u} A) :=
        (derivedSectionsOver X.toRingedSpace ρ).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
              (limit (quotientTower X ρ f ℱ)))
      Nonempty (Fhat ≅ completed.obj (derivedSectionsModule X ρ ℱ)) ∧
        IsDerivedComplete (Ideal.span {f}) Fhat ∧
        ∀ p : ℤ, Nonempty
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj Fhat ≅
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
              (completed.obj (derivedSectionsModule X ρ ℱ))) := by
  intro P completion adj completed Fhat
  obtain ⟨e⟩ := nonempty_iso_koszulTower_comp_derivedSections X ρ f ℱ
  obtain ⟨_, hFhat⟩ := isDerivedLimit_single_limit_Csys X ρ f ℱ hℱ
  obtain ⟨Ehat, hEhat⟩ := exists_isDerivedLimit (Ksys (mulF X ρ f ℱ))
  -- `Ehat ≅ lim ℱ/f^(n+1)ℱ` in degree zero, by the pro-isomorphism of Tag 0H3D.
  obtain ⟨eEF⟩ := nonempty_iso_isDerivedLimit_koszulTower_quotientTower
    X.toRingedSpace ρ f ℱ hstab _ _ hEhat hFhat
  -- `RΓ(X, Ehat)` is a derived limit of the tower of derived sections, by Tag 0D60.
  obtain ⟨_, hRΓ⟩ := isDerivedLimit_map_derivedSectionsOver
    X.toRingedSpace ρ (Ksys (mulF X ρ f ℱ)) Ehat hEhat
  -- That tower is the `f`-power Koszul tower of `RΓ(X, ℱ)` over `A`, by Tag 0H3C.
  have hRΓ' : IsDerivedLimit
      (PrincipalTorsionTower.principalDerivedTensorSystem A f (derivedSectionsModule X ρ ℱ))
      ((derivedSectionsOver X.toRingedSpace ρ).obj Ehat) :=
    IsDerivedLimit.of_natIso e hRΓ
  -- The mapping-cocone model of the Milnor limit is another derived limit of that same tower.
  have hmil : IsDerivedLimit
      (PrincipalTorsionTower.principalDerivedTensorSystem A f (derivedSectionsModule X ρ ℱ))
      ((CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f
        (DerivedCategory.Q.objPreimage (derivedSectionsModule X ρ ℱ)))).obj₁) :=
    isDerivedLimit_milnorTriangle_obj₁ A _
  -- Two derived limits of one system are isomorphic, by Tag 07KZ.
  obtain ⟨eu⟩ := (ModuleDerivedLimitTriangle.derivedLimit_iso_and_homology_shortExact A
    (PrincipalTorsionTower.principalDerivedTensorSystem A f
      (derivedSectionsModule X ρ ℱ))).1 _ _ hRΓ' hmil
  -- The derived completion is that same mapping-cocone model, by Tag 0BKG.
  obtain ⟨S, -⟩ := CompletionSequences.derivedCompletion_principal_homology A f completion adj
  have eFhat : Fhat ≅ completed.obj (derivedSectionsModule X ρ ℱ) :=
    (derivedSectionsOver X.toRingedSpace ρ).mapIso eEF.symm ≪≫ eu ≪≫
      (S.comparison.iso (DerivedCategory.Q.objPreimage (derivedSectionsModule X ρ ℱ))).symm ≪≫
      completed.mapIso (DerivedCategory.Q.objObjPreimageIso (derivedSectionsModule X ρ ℱ))
  refine ⟨⟨eFhat⟩, ?_, fun p ↦ ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).mapIso
    eFhat⟩⟩
  exact DerivedCompleteRecurrence.isDerivedComplete_of_iso eFhat.symm
    (P.prop_ι_obj (completion.obj (derivedSectionsModule X ρ ℱ)))

end Stacks.Algebraization.PrincipalQuotientTowerCompletion

end
