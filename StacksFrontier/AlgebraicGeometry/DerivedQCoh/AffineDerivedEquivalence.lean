module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Inclusion
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.TildeFactorization
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived Spec–Γ equivalence on an affine scheme

Let `R` be a commutative ring. This file proves that derived sheafification
`AlgebraicGeometry.derivedTilde : D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence of triangulated
categories, and hence that the comparison functor
`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison` of
[Stacks, Tag 06VT] is an equivalence on an affine scheme — the assertion of
[Stacks, Tag 08D9] part (3) and the remaining content of [Stacks, Tag 06Z0] beyond its `~` edge.

The route is the adjunction. `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` exhibits
derived sheafification as left adjoint to unbounded derived global sections, and restricting the
right adjoint to `D_QCoh(𝒪_{Spec R})` makes the adjunction one between `D(R)` and
`D_QCoh(𝒪_{Spec R})`. Its unit is invertible by unbounded affine vanishing
(`AlgebraicGeometry.quasiIso_globalSectionsOver_map_tilde`), which makes derived sheafification
fully faithful, and its right adjoint kills no nonzero object
(`AlgebraicGeometry.isZero_homology_of_isZero_homology_globalSectionsOver`). A fully faithful exact
functor of triangulated categories whose right adjoint has zero kernel is an equivalence
([Stacks, Tag 09J1]), which closes the argument.

`AlgebraicGeometry.derivedTilde_isEquivalence` is registered as an instance, so the affine duality
statements that carry `[(derivedTilde R).IsEquivalence]` as a hypothesis —
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjoint.lean` among them —
need no argument once this file is imported.

## Main definitions

* `AlgebraicGeometry.derivedTildeQuasicoherentAdjunction` — derived sheafification is left adjoint
  to the restriction of `RΓ(Spec R, -)` to `D_QCoh(𝒪_{Spec R})`.

## Main results

* `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit` — the unit of the derived
  Spec–Γ adjunction is invertible.
* `AlgebraicGeometry.derivedTilde_isEquivalence` — derived sheafification
  `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence.
* `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent_isEquivalence` — so is unbounded derived
  global sections `D_QCoh(𝒪_{Spec R}) ⥤ D(R)`.
* `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` — the counit of the
  derived Spec–Γ adjunction is invertible at every object with quasi-coherent cohomology.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` — the comparison functor of
  [Stacks, Tag 06VT] is an equivalence on an affine scheme.
* `Stacks.DerivedQCoh.isEquivalenceOntoDQCoh` — the functor (06VT) itself, before its
  factorization through `D_QCoh(𝒪_{Spec R})`, is full, is faithful and has essential image
  exactly the objects with quasi-coherent cohomology. This discharges
  `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, whose consumers get unconditional forms here:
  `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh'` and
  `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTilde'`.

## Implementation notes

**No `08D9` attribute is placed.** The result below is the *first* assertion of
[Stacks, Tag 08D9] part (3), that the functor (06VT) is an equivalence. The tag asserts in
addition that the quasi-inverse is the derived coherator `RQ_X` and, in its parts (1) and (2),
computes the coherator and its derived functor on an affine scheme; the coherator of
[Stacks, Tag 08D8] is not in this library, so neither part (1), nor part (2), nor the
identification of the quasi-inverse in part (3) is available, and the covering set of that tag is
therefore incomplete. An attribute placed now would report it as formalized on the strength of
part of its content.

**The `06Z0` attributes are placed.** All thirteen declarations of the decomposition of
[Stacks, Tag 06Z0] are proved, the last of them — the normalization of the degree-zero
isomorphism `H⁰(X, E) ≅ Γ(X, H⁰(E))` on global cycles — being
`AlgebraicGeometry.globalSectionsCyclesToHomology_comp_derivedGlobalSectionsHomologyZeroIso` in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/DegreeZeroCohomology.lean`, so each of the thirteen
carries `@[stacks 06Z0]` with its clause label. The roll-call, with a citation for each, is in
the implementation notes of `StacksFrontier/AlgebraicGeometry/DerivedTilde.lean`.

**The model.** Everything is at the locally small derived categories
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`, which is
the model `AlgebraicGeometry.derivedTilde` and the affine duality statements are stated at. The
two inputs from
`StacksFrontier/AlgebraicGeometry/AffineVanishingQuasicoherentComplex.lean` are proved at
`CategoryTheory.HasDerivedCategory.standard` but stated without any derived category, which is
exactly what lets them be used here; see the implementation notes of that file.

**Restricting the adjunction.** `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is an
adjunction between `D(R)` and the *whole* `D(𝒪_{Spec R})`, since its left adjoint is
`derivedTilde R` followed by the inclusion of `D_QCoh(𝒪_{Spec R})`. Its counit is *not*
invertible — `RΓ(Spec R, E)^~ ⟶ E` fails to be an isomorphism as soon as `E` has a cohomology
sheaf that is not quasi-coherent — so the adjunction itself is not an equivalence and the
restriction along the fully faithful inclusion, `CategoryTheory.Adjunction.restrictFullyFaithful`,
is what produces an adjunction whose two sides are the categories of [Stacks, Tag 06Z0].

## References

* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry

universe w₁ w₂ u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) [HasDerivedCategory.{w₁} (Spec R).Modules]
  [HasDerivedCategory.{w₂} (ModuleCat.{u} R)]

/-- **The unit of the derived Spec–Γ adjunction is invertible.** For every object `M` of `D(R)`
the canonical map `M ⟶ RΓ(Spec R, M^~)` is an isomorphism.

This is `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso` fed
with unbounded affine vanishing for the complexes `M̃^•`, which is
`AlgebraicGeometry.quasiIso_globalSectionsOver_map_tilde`. -/
@[stacks 06Z0 "canonical unit isomorphism"]
theorem isIso_derivedTildeGlobalSectionsAdjunction_unit :
    IsIso (derivedTildeGlobalSectionsAdjunction R).val.unit := by
  have h : ∀ M : DerivedCategory (ModuleCat.{u} R),
      IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M) := fun M =>
    isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso R
      (fun M' I s hI hs => quasiIso_globalSectionsOver_map_tilde R M' s hI hs) M
  exact NatIso.isIso_of_isIso_app _

/-- **Derived sheafification is left adjoint to derived global sections on
`D_QCoh(𝒪_{Spec R})`.** The restriction of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` along the fully faithful inclusion of
`D_QCoh(𝒪_{Spec R})` into `D(𝒪_{Spec R})`: both sides are now the two categories compared by
[Stacks, Tag 06Z0]. -/
def derivedTildeQuasicoherentAdjunction :
    derivedTilde R ⊣ derivedGlobalSectionsQuasicoherent R :=
  Adjunction.restrictFullyFaithful (derivedTildeGlobalSectionsAdjunction R).val
    (Functor.FullyFaithful.id _)
    ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).fullyFaithfulι)
    (Functor.leftUnitor _) (Functor.rightUnitor _).symm

/-- Derived sheafification is fully faithful: the unit of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is invertible, so derived sheafification
followed by the inclusion of `D_QCoh(𝒪_{Spec R})` is fully faithful, and the inclusion is
faithful. -/
instance derivedTilde_faithful : (derivedTilde R).Faithful := by
  have := isIso_derivedTildeGlobalSectionsAdjunction_unit R
  have h : (derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).FullyFaithful :=
    Adjunction.fullyFaithfulLOfIsIsoUnit (derivedTildeGlobalSectionsAdjunction R).val
  have := h.faithful
  exact Functor.Faithful.of_comp _ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι

/-- Derived sheafification is full; see `AlgebraicGeometry.derivedTilde_faithful`. -/
instance derivedTilde_full : (derivedTilde R).Full := by
  have := isIso_derivedTildeGlobalSectionsAdjunction_unit R
  have h : (derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).FullyFaithful :=
    Adjunction.fullyFaithfulLOfIsIsoUnit (derivedTildeGlobalSectionsAdjunction R).val
  have := h.full
  exact Functor.Full.of_comp_faithful _ (DerivedCategoryB.derivedCategoryB
    (A := (Spec R).Modules) (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι

/-- **Derived global sections has zero kernel on `D_QCoh(𝒪_{Spec R})`.** An object of
`D(𝒪_{Spec R})` whose cohomology sheaves are quasi-coherent and whose derived global sections
vanish is itself zero.

Represent the object as `Q K`; derived global sections of `Q K` is the complex of global sections
of a K-injective resolution `I` of `K`, whose vanishing forces `K` to be acyclic by
`AlgebraicGeometry.isZero_homology_of_isZero_homology_globalSectionsOver`. -/
theorem isZero_of_isZero_derivedGlobalSectionsQuasicoherent_obj
    (Z : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (hZ : IsZero ((derivedGlobalSectionsQuasicoherent R).obj Z)) : IsZero Z := by
  obtain ⟨K, ⟨e⟩⟩ : (DerivedCategory.Q (C := (Spec R).Modules)).essImage Z.obj :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) Z.obj
  obtain ⟨I, s, hI, hs⟩ := Scheme.Modules.exists_quasiIso_isKInjective (Spec R) K
  -- the cohomology of `K` is that of `Z`, hence quasi-coherent
  have eHom : ∀ n : ℤ, (DerivedCategory.homologyFunctor (Spec R).Modules n).obj Z.obj ≅
      K.homology n := fun n =>
    (DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (Spec R).Modules n).app K
  have hK : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso (eHom n) (Z.2 n)
  -- `RΓ(Q K) = 0`
  have hRΓ : IsZero ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)) :=
    IsZero.of_iso hZ ((derivedGlobalSectionsOver (𝟙 (Spec R))).mapIso e)
  -- so the global sections of `I` are acyclic
  have hsQ : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := (Spec R).Modules) s).2 hs
  have hcmp : IsIso (globalSectionsComplexComparison (𝟙 (Spec R)) I) :=
    isIso_globalSectionsComplexComparison_of_isKInjective (𝟙 (Spec R)) hI
  have hac : ∀ n : ℤ, IsZero ((((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology n) := by
    intro n
    have hzero : IsZero (DerivedCategory.Q.obj
        (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :=
      IsZero.of_iso (IsZero.of_iso hRΓ
          ((derivedGlobalSectionsOver (𝟙 (Spec R))).mapIso
            (asIso (DerivedCategory.Q.map s))).symm)
        (asIso (globalSectionsComplexComparison (𝟙 (Spec R)) I))
    exact IsZero.of_iso
      (Stacks.SmallDerivedCategory.isZero_homologyFunctor_obj_of_isZero hzero n)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app _).symm
  -- hence `K` is acyclic, hence `Z` is zero
  have hKzero : ∀ n : ℤ, IsZero (K.homology n) := fun n =>
    isZero_homology_of_isZero_homology_globalSectionsOver R K hK s hI hs hac n
  have hobj : IsZero Z.obj :=
    Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj Z.obj fun n =>
      IsZero.of_iso (hKzero n) (eHom n)
  rw [IsZero.iff_id_eq_zero]
  exact ObjectProperty.hom_ext _ (by
    rw [show ((𝟙 Z : Z ⟶ Z)).hom = 𝟙 Z.obj from rfl, hobj.eq_of_src (𝟙 Z.obj) 0]
    rfl)

/-- **Derived sheafification is an equivalence** `D(R) ≌ D_QCoh(𝒪_{Spec R})`. This is the
remaining content of [Stacks, Tag 06Z0] for the two edges `~` and (06VT) of its triangle.

Derived sheafification is exact and fully faithful, and its right adjoint, derived global
sections, has zero kernel; by [Stacks, Tag 09J1] that is enough. -/
@[stacks 06Z0 "sheafification equivalence"]
instance derivedTilde_isEquivalence : (derivedTilde R).IsEquivalence :=
  isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero (derivedTilde R)
    (derivedGlobalSectionsQuasicoherent R) (derivedTildeQuasicoherentAdjunction R)
    (isZero_of_isZero_derivedGlobalSectionsQuasicoherent_obj R)

/-- **Unbounded derived global sections `D_QCoh(𝒪_{Spec R}) ⥤ D(R)` is an equivalence**, being
right adjoint to the equivalence `AlgebraicGeometry.derivedTilde`. This is the `RΓ(X, -)` edge of
the triangle of [Stacks, Tag 06Z0]. -/
@[stacks 06Z0 "global sections equivalence"]
theorem derivedGlobalSectionsQuasicoherent_isEquivalence :
    (derivedGlobalSectionsQuasicoherent R).IsEquivalence :=
  have := derivedTilde_isEquivalence R
  (derivedTildeQuasicoherentAdjunction R).isEquivalence_right_of_isEquivalence_left

/-- **The counit of the derived Spec–Γ adjunction is invertible on `D_QCoh(𝒪_{Spec R})`.** For
every object `E` of `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves the canonical map
`RΓ(Spec R, E)^~ ⟶ E` is an isomorphism.

The left adjoint `derivedTilde R ⋙ ι` is fully faithful, the unit being invertible, so its counit
is invertible exactly on its essential image; and `E` is in that essential image because derived
sheafification is essentially surjective onto `D_QCoh(𝒪_{Spec R})`. The restriction to objects
with quasi-coherent cohomology cannot be dropped: `RΓ(Spec R, E)^~ ⟶ E` fails to be invertible as
soon as some cohomology sheaf of `E` is not quasi-coherent, which is why the adjunction itself is
not an equivalence. -/
@[stacks 06Z0 "canonical counit isomorphism"]
theorem isIso_derivedTildeGlobalSectionsAdjunction_counit_app
    (E : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app
      ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj E)) := by
  have := isIso_derivedTildeGlobalSectionsAdjunction_unit R
  have hff : (derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι).FullyFaithful :=
    Adjunction.fullyFaithfulLOfIsIsoUnit (derivedTildeGlobalSectionsAdjunction R).val
  have := hff.full
  have := hff.faithful
  have := derivedTilde_isEquivalence R
  obtain ⟨M, ⟨e⟩⟩ : (derivedTilde R).essImage E :=
    Functor.EssSurj.mem_essImage (F := derivedTilde R) E
  exact Adjunction.isIso_counit_app_of_iso _
    ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.mapIso e.symm)

end AlgebraicGeometry

namespace Stacks.DerivedQCoh

open Stacks.AlgebraicGeometry.QuasicoherentDerived

/-- **The comparison functor of [Stacks, Tag 06VT] is an equivalence on an affine scheme.** The
canonical functor `D(QCoh(𝒪_{Spec R})) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence of triangulated
categories.

This is the first assertion of [Stacks, Tag 08D9] part (3). It is
`Stacks.DerivedQCoh.derivedTilde_isEquivalence_iff_comparison` applied to
`AlgebraicGeometry.derivedTilde_isEquivalence`: the `~` edge of [Stacks, Tag 06Z0] is an
equivalence of abelian categories, so the comparison functor is an equivalence exactly when
derived sheafification is. -/
@[stacks 06Z0 "comparison equivalence"]
theorem derivedQuasicoherentComparison_isEquivalence (R : CommRingCat.{u}) :
    (derivedQuasicoherentComparison.{u} (Spec R)).IsEquivalence :=
  (derivedTilde_isEquivalence_iff_comparison R).mp
    (AlgebraicGeometry.derivedTilde_isEquivalence R)

/-- **The functor (06VT) of Stacks 06Z0 is an equivalence onto `D_QCoh(𝒪_{Spec A})`.** On an
affine scheme `Stacks.DerivedQCoh.derivedQCohι : D(QCoh(𝒪_{Spec A})) ⥤ D(𝒪_{Spec A})` is full, is
faithful, and its essential image is exactly the objects all of whose cohomology sheaves are
quasi-coherent. This is `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`.

The functor factors as the comparison functor of [Stacks, Tag 06VT] followed by the inclusion of
`D_QCoh(𝒪_{Spec A})`, by `Stacks.DerivedQCoh.derivedQuasicoherentComparisonCompι`. The comparison
is an equivalence by `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` and the
inclusion of a strictly full subcategory is fully faithful with essential image its own objects,
so the composite is fully faithful with essential image `D_QCoh(𝒪_{Spec A})`; the containment
half of the last clause is `Stacks.DerivedQCoh.isDQCoh_of_essImage_derivedQCohι` and needs none of
this. -/
@[sga "6 II 3.7" "Clause b), special case"]
theorem isEquivalenceOntoDQCoh (A : CommRingCat.{u}) : IsEquivalenceOntoDQCoh.{u, u} A := by
  have hc := derivedQuasicoherentComparison_isEquivalence A
  have e : derivedQuasicoherentComparison.{u} (Spec A) ⋙
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).ι ≅ derivedQCohι A :=
    derivedQuasicoherentComparisonCompι.{u} (Spec A)
  refine ⟨Functor.Full.of_iso e, Functor.Faithful.of_iso e, fun E =>
    ⟨isDQCoh_of_essImage_derivedQCohι A, fun hE => ?_⟩⟩
  obtain ⟨F, ⟨eF⟩⟩ := Functor.EssSurj.mem_essImage
    (F := derivedQuasicoherentComparison.{u} (Spec A))
    (⟨E, hE⟩ : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).FullSubcategory)
  exact ⟨F, ⟨(e.app F).symm ≪≫ (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)).ι.mapIso eF⟩⟩

/-- **Every object of `D_QCoh(𝒪_{Spec A})` is the complex of quasi-coherent sheaves attached to
an object of `D(A)`.** This is `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh` with its
hypothesis discharged by `Stacks.DerivedQCoh.isEquivalenceOntoDQCoh`. -/
theorem exists_iso_derivedTilde_of_isDQCoh' (A : CommRingCat.{u})
    {E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf)}
    (hE : IsDQCoh (R := (Spec A).ringCatSheaf) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} A),
      Nonempty ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M) ≅ E) :=
  exists_iso_derivedTilde_of_isDQCoh A
    (fun E' hE' => ((isEquivalenceOntoDQCoh A).2.2 E').2 hE') hE

/-- **`D_QCoh(𝒪_{Spec A})` consists exactly of the complexes attached to objects of `D(A)`.**
This is `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTilde` with its hypothesis discharged by
`Stacks.DerivedQCoh.isEquivalenceOntoDQCoh`. -/
theorem isDQCoh_iff_exists_iso_derivedTilde' (A : CommRingCat.{u})
    (E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf)) :
    IsDQCoh (R := (Spec A).ringCatSheaf) E ↔
      ∃ M : DerivedCategory (ModuleCat.{u} A),
        Nonempty ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M) ≅ E) :=
  isDQCoh_iff_exists_iso_derivedTilde A
    (fun E' hE' => ((isEquivalenceOntoDQCoh A).2.2 E').2 hE') E

end Stacks.DerivedQCoh

end
