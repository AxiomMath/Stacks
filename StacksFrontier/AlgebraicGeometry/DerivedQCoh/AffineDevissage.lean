module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineComparisonTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceModulesAbelian
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EssentialImage
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility

/-!
# Dévissage of `D_QCoh(𝒪_Y)` on an affine scheme

Let `Y` be an affine scheme. This file proves that a property `T` of objects of `D(𝒪_Y)` holds at
every object with quasi-coherent cohomology as soon as it

* is invariant under isomorphism,
* passes to a direct sum of a family of objects of `D_QCoh(𝒪_Y)`,
* satisfies two-out-of-three on distinguished triangles, and
* holds at every shift of the structure sheaf placed in degree zero.

This is the affine core of the dévissage in the source's proof of [Stacks, Tag 08EU]
(Lemma 36.22.1). There the three functors of the projection formula are checked to commute with
direct sums and to be exact, which reduces the assertion to `K` a direct sum of shifts of `𝒪_Y`,
and then to `K = 𝒪_Y[k]` where the claim is immediate. The source's words for the step formalized
here are: *the functor `~ : D(A) → D_QCoh(𝒪_Y)` is an equivalence (Lemma 36.3.5) … the discussion
above and More on Algebra, Remark 15.60.11 shows that it suffices to prove `T` holds for `A[k]`.*

## The route

The dévissage itself is not redone. [Stacks, Tag 09PB] already provides it for the derived
category of a ring, as
`CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`, and the content of
this file is the transport of that statement along

`affineTilde Y : D(Γ(Y, ⊤)) ⥤ D(𝒪_Y)`,

derived sheafification followed by restriction along `AlgebraicGeometry.Scheme.isoSpec`. Four
things make the transport work.

* `affineTilde Y` is an exact functor of triangulated categories which preserves direct sums: the
  first factor is a left adjoint, by the derived Spec–Γ adjunction, and the second is an
  equivalence, restriction along an isomorphism of schemes.
* Its image has quasi-coherent cohomology sheaves
  (`AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj`, and quasi-coherence is
  preserved by restriction). This is what lets the hypothesis on direct sums be stated for
  quasi-coherent families only, which is the shape the dévissage of [Stacks, Tag 08EU] needs.
* `affineTilde Y` of the regular module in degree zero is `𝒪_Y[0]`, which carries the base case
  from `A[k]` to the shifts of the structure sheaf.
* Every object of `D(𝒪_Y)` with quasi-coherent cohomology lies in the image, by the counit clause
  of [Stacks, Tag 06Z0], `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`:
  the counit exhibits such an object as the derived sheafification of its derived global sections.

## Main results

* `Stacks.DerivedQCoh.property_of_isDQCoh_of_isAffine` — the dévissage.

## Implementation notes

No `@[stacks 08EU]` attribute is placed. This is one step of the source's proof of that lemma and
not a clause of its statement; the registered clauses of the tag live in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaInvertibility.lean`.

The statement is at `CategoryTheory.HasDerivedCategory.standard`, which is the model
`Stacks.Cohomology.DerivedProjectionFormula.singleUnit` and the counit clause of
[Stacks, Tag 06Z0] are stated at, and the category of modules is spelled
`SheafOfModules (structureSheafRing Y.toRingedSpace)` for the same reason. That is the same
category as `AlgebraicGeometry.Scheme.Modules Y`, which the `tilde` API lands in, but the two
spellings meet only at default transparency; the `implicit_reducible` attributes below are what
let the rewrites inside the proof see through them.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u w

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf

attribute [local instance] preservesFiniteLimits_restrictFunctor

/-! ### The generic dévissage along a triangulated functor out of `D(R)` -/

/-- **The dévissage of [Stacks, Tag 09PB] transported along a triangulated functor.** Let
`Φ : D(R) ⥤ D(A)` be an exact functor of triangulated categories and `T` a property of objects of
`D(A)` which is invariant under isomorphism, satisfies two-out-of-three on distinguished triangles,
holds at `Φ` of every shift of the regular module, and passes to `Φ` of a direct sum whenever it
holds at each summand. Then `T` holds at `Φ(M)` for every `M` in `D(R)`.

This is `CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts` applied to the
pulled-back property `N ↦ T (Φ N)`: the coproduct clause is the hypothesis, the shift clause is the
hypothesis, and the triangle clause holds because `Φ` carries a distinguished triangle of `D(R)` to
one of `D(A)`.

The target is spelled `DerivedCategory A` rather than an abstract triangulated category. The two
statements are mathematically the same, but the abstract one cannot be *used*: its
`[∀ n : ℤ, (shiftFunctor D n).Additive]` binder is not synthesized at a call site where `D` is
`DerivedCategory Y.Modules`, even though that very instance is found by `inferInstance` when asked
for on its own. Spelling the target as a derived category removes the binder, and with it the
failure. -/
private theorem property_of_devissage {R : Type u} [Ring R] [Small.{u} R]
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (Φ : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory A)
    [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (T : DerivedCategory A → Prop)
    (hsum : ∀ {I : Type u} (Z : I → DerivedCategory (ModuleCat.{u} R)) [HasCoproduct Z],
      (∀ i, T (Φ.obj (Z i))) → T (Φ.obj (∐ Z)))
    (htri : ∀ Δ : Pretriangulated.Triangle (DerivedCategory A),
      Δ ∈ Pretriangulated.distinguishedTriangles →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
        (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁))
    (hunit : ∀ k : ℤ, T (Φ.obj (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (Shrink.{u} R)))⟦k⟧)))
    (M : DerivedCategory (ModuleCat.{u} R)) : T (Φ.obj M) :=
  CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts.2
    (fun N => T (Φ.obj N)) (fun Z _ => hsum Z)
    (fun Δ hΔ => htri (Φ.mapTriangle.obj Δ) (Φ.map_distinguished Δ hΔ)) hunit M

/-! ### Restriction of modules along a morphism of schemes and `D_QCoh` -/

/-- **`D_QCoh` is stable under restriction along an open immersion.** Restriction is exact, so it
commutes with the cohomology functors of the derived category, and it carries a quasi-coherent
module to a quasi-coherent one. -/
private theorem isDQCoh_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (K : DerivedCategory Y.Modules) (hK : IsDQCoh (R := Y.ringCatSheaf) K) :
    IsDQCoh (R := X.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor f).mapDerivedCategory.obj K) := by
  intro n
  have h1 : ((DerivedCategory.homologyFunctor Y.Modules n).obj K).IsQuasicoherent := hK n
  have h2 : SheafOfModules.isQuasicoherent X.ringCatSheaf
      ((Scheme.Modules.restrictFunctor f).obj
        ((DerivedCategory.homologyFunctor Y.Modules n).obj K)) :=
    Scheme.Modules.isQuasicoherent_restrictFunctor f _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.restrictFunctor f) n).app K).symm h2

/-! ### The functor `D(Γ(Y, ⊤)) ⥤ D(𝒪_Y)` on an affine scheme -/

/-- The functor of `modulesRestrictionEquivalence` is additive, being restriction along a
morphism of schemes. -/
private instance additive_modulesRestrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    (modulesRestrictionEquivalence e).functor.Additive :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor e.inv).Additive)

/-- Derived sheafification followed by restriction along `Y ≅ Spec Γ(Y, ⊤)`. -/
private abbrev affineTilde (Y : Scheme.{u}) [IsAffine Y] :
    DerivedCategory (ModuleCat.{u} Γ(Y, ⊤)) ⥤ DerivedCategory Y.Modules :=
  (tilde.functor Γ(Y, ⊤)).mapDerivedCategory ⋙
    (Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapDerivedCategory

/-- `affineTilde Y` commutes with the shift, both of its factors being derived functors of exact
functors. -/
private instance commShift_affineTilde (Y : Scheme.{u}) [IsAffine Y] :
    (affineTilde Y).CommShift ℤ :=
  inferInstanceAs (((tilde.functor Γ(Y, ⊤)).mapDerivedCategory ⋙
    (Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapDerivedCategory).CommShift ℤ)

/-- `affineTilde Y` is an exact functor of triangulated categories. -/
private instance isTriangulated_affineTilde (Y : Scheme.{u}) [IsAffine Y] :
    (affineTilde Y).IsTriangulated :=
  inferInstanceAs (((tilde.functor Γ(Y, ⊤)).mapDerivedCategory ⋙
    (Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapDerivedCategory).IsTriangulated)

/-- Derived sheafification is a left adjoint, by the derived Spec–Γ adjunction. -/
private instance isLeftAdjoint_tildeMapDerivedCategory (R : CommRingCat.{u}) :
    ((tilde.functor R).mapDerivedCategory).IsLeftAdjoint :=
  (Adjunction.ofNatIsoLeft (derivedTildeGlobalSectionsAdjunction R).val
    (derivedTildeCompι R)).isLeftAdjoint

/-- Restriction along `Y ≅ Spec Γ(Y, ⊤)` induces an equivalence of derived categories. -/
private instance isEquivalence_restrictIsoSpec (Y : Scheme.{u}) [IsAffine Y] :
    ((Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapDerivedCategory).IsEquivalence :=
  (Equivalence.mapDerivedCategory
    (modulesRestrictionEquivalence Y.isoSpec)).isEquivalence_inverse

/-- `affineTilde Y` preserves direct sums indexed by any type in `Type u`: its first factor is a
left adjoint and its second is an equivalence. -/
private instance preservesColimitsOfShape_affineTilde (Y : Scheme.{u}) [IsAffine Y]
    (I : Type u) : PreservesColimitsOfShape (Discrete I) (affineTilde Y) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete I)
    ((tilde.functor Γ(Y, ⊤)).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapDerivedCategory))

/-- The image of `affineTilde Y` has quasi-coherent cohomology sheaves. -/
private theorem isDQCoh_affineTilde_obj (Y : Scheme.{u}) [IsAffine Y]
    (X : DerivedCategory (ModuleCat.{u} Γ(Y, ⊤))) :
    IsDQCoh (R := Y.ringCatSheaf) ((affineTilde Y).obj X) :=
  isDQCoh_restrict Y.isoSpec.hom _
    (fun n => isQuasicoherent_homology_mapDerivedCategory_obj Γ(Y, ⊤) X n)

/-- **The base case: the tilde of the regular module is the structure sheaf.** -/
private def affineTildeUnitIso (Y : Scheme.{u}) [IsAffine Y] :
    (affineTilde Y).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y, ⊤)) 0).obj
        (ModuleCat.of ↥Γ(Y, ⊤) (Shrink.{u} ↥Γ(Y, ⊤)))) ≅
      Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y.toRingedSpace :=
  (Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategorySingleFunctor (tilde.functor Γ(Y, ⊤)) 0).app
        (ModuleCat.of ↥Γ(Y, ⊤) (Shrink.{u} ↥Γ(Y, ⊤)))) ≪≫
    (Functor.mapDerivedCategorySingleFunctor
        (Scheme.Modules.restrictFunctor Y.isoSpec.hom) 0).app _ ≪≫
    (DerivedCategory.singleFunctor Y.Modules 0).mapIso
      ((Scheme.Modules.restrictFunctor Y.isoSpec.hom).mapIso
          ((tilde.functor Γ(Y, ⊤)).mapIso
            (Shrink.linearEquiv ↥Γ(Y, ⊤) ↥Γ(Y, ⊤)).toModuleIso ≪≫ tildeSelf) ≪≫
        Scheme.Modules.restrictUnitIso Y.isoSpec.hom)

/-- **The affine core of the dévissage of [Stacks, Tag 08EU].** Let `Y` be an affine scheme and
`T` a property of objects of `D(𝒪_Y)` which is invariant under isomorphism, passes to a direct sum
of a family of objects with quasi-coherent cohomology, satisfies two-out-of-three on distinguished
triangles, and holds at every shift of the structure sheaf placed in degree zero. Then `T` holds at
every object of `D(𝒪_Y)` whose cohomology sheaves are all quasi-coherent.

The proof transports `CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`
([Stacks, Tag 09PB]) along `affineTilde Y`; see the implementation notes of this file for the four
inputs that make the transport work. -/
theorem property_of_isDQCoh_of_isAffine {Y : Scheme.{u}} [IsAffine Y]
    (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) → Prop)
    (hiso : ∀ {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))},
      (A ≅ B) → T A → T B)
    (hsum : ∀ {I : Type u}
      (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
      [HasCoproduct Z],
      (∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) (Z i)) →
      (∀ i, T (Z i)) → T (∐ Z))
    (htri : ∀ Δ : CategoryTheory.Pretriangulated.Triangle
        (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))),
      Δ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
        (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁))
    (hunit : ∀ m : ℤ,
      T ((Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y.toRingedSpace)⟦m⟧))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    T K := by
  -- the restriction equivalence `D(𝒪_Y) ≌ D(𝒪_{Spec Γ(Y, ⊤)})`
  let ED := Equivalence.mapDerivedCategory (modulesRestrictionEquivalence Y.isoSpec)
  have hisoY : ∀ {A B : DerivedCategory Y.Modules}, (A ≅ B) → T A → T B := hiso
  -- the hypotheses of the dévissage, transported along `affineTilde Y`
  have hΦsum : ∀ {I : Type u} (Z : I → DerivedCategory (ModuleCat.{u} Γ(Y, ⊤)))
      [HasCoproduct Z], (∀ i, T ((affineTilde Y).obj (Z i))) →
      T ((affineTilde Y).obj (∐ Z)) := by
    intro I Z _ hZ
    exact hisoY (Limits.PreservesCoproduct.iso (affineTilde Y) Z).symm
      (hsum (fun i => (affineTilde Y).obj (Z i))
        (fun i => isDQCoh_affineTilde_obj Y (Z i)) hZ)
  have hΦunit : ∀ k : ℤ, T ((affineTilde Y).obj (((DerivedCategory.singleFunctor
      (ModuleCat.{u} Γ(Y, ⊤)) 0).obj
      (ModuleCat.of ↥Γ(Y, ⊤) (Shrink.{u} ↥Γ(Y, ⊤))))⟦k⟧)) := fun k =>
    hisoY ((shiftFunctor (DerivedCategory Y.Modules) k).mapIso
      (affineTildeUnitIso Y).symm ≪≫ (((affineTilde Y).commShiftIso k).app _).symm) (hunit k)
  -- essential surjectivity: the counit of the derived Spec–Γ adjunction
  have hKq : IsDQCoh (R := (Spec Γ(Y, ⊤)).ringCatSheaf) (ED.functor.obj K) :=
    isDQCoh_restrict Y.isoSpec.inv K hK
  have hco := AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso Γ(Y, ⊤)
    ⟨ED.functor.obj K, hKq⟩
  have eK : (affineTilde Y).obj ((derivedGlobalSectionsOver
      (𝟙 (Spec Γ(Y, ⊤)))).obj (ED.functor.obj K)) ≅ K :=
    ED.inverse.mapIso (((derivedTildeCompι Γ(Y, ⊤)).app _).symm ≪≫
      @asIso _ _ _ _ _ hco) ≪≫ (ED.unitIso.app K).symm
  exact hisoY eK (property_of_devissage (affineTilde Y) T hΦsum htri hΦunit _)

end Stacks.DerivedQCoh

end
