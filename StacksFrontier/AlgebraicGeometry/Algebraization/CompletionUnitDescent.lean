module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationLocalCohomologyLimit
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.Dualizing.Ext
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.RestrictScalars

/-!
# Descent of the derived completion unit along a flat map which is an isomorphism mod `I`

Let `A → B` be a flat homomorphism of commutative rings inducing an isomorphism `A/I ≅ B/IB`
for a finitely generated ideal `I ⊆ A` — the situation of Stacks 05E9 and Stacks 0925, of which
`A → A^∧` is the example this file is built for. For an object `L` of `D(B)` whose cohomology is
`IB`-power torsion, the derived `I`-adic completion of the restriction of scalars of `L` is the
restriction of scalars of the derived `IB`-adic completion of `L`, compatibly with the two
completion units. Consequently invertibility of the completion unit on cohomology descends from
`B` to `A`.

Applied to the `I`-adic completion `A' = A^∧` of a Noetherian local ring and to
`L = RΓ_{𝔪'}(M')`, this is the third paragraph of the proof of **Stacks 0EFR**: the first display
of that proof, which Stacks 0DXP supplies over `A'` only, is carried back down to `A`. Together
with Stacks 0DXJ it gives both assertions of Stacks 0EFR over `A` itself, with no completeness
assumption.

## Main results

* `Stacks.Algebraization.isIso_derivedExtensionUnit_of_derivedPowerTorsion` — the unit
  `X ⟶ (X ⊗ᴸ_A B)_A` of the derived extension–restriction adjunction is invertible at an object
  of `D(A)` with `I`-power-torsion cohomology. This is the derived form of Stacks 05E9.
* `Stacks.Algebraization.isIso_derivedExtensionCounit_of_derivedPowerTorsion` — the counit is
  invertible at an object of `D(B)` with `IB`-power-torsion cohomology.
* `Stacks.Algebraization.bijective_restrictScalars_map_of_derivedPowerTorsion` — restriction of
  scalars is bijective on morphisms out of an object of `D(B)` with `IB`-power-torsion
  cohomology.
* `Stacks.Algebraization.exists_iso_adicCompletion_restrictScalars` — the derived completion of
  the restriction of scalars of such an object is the restriction of scalars of its derived
  completion, compatibly with the units.
* `Stacks.Algebraization.isIso_homology_adicCompletionUnit_restrictScalars` — invertibility of
  the completion unit on cohomology descends along restriction of scalars.
* `Stacks.Algebraization.nonempty_iso_localCohomology_restrictScalars_adicCompletion` — for a
  Noetherian ring, an ideal `I ⊆ J` and a finite module `M`, local cohomology `RΓ_J(M)` is the
  restriction of scalars of `RΓ_{J A'}(M')` over the `I`-adic completion `A'`.
* `Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint`
  — the first display of the proof of Stacks 0EFR over `A` itself, with no completeness
  assumption.
* `Stacks.Algebraization.isIso_localCohomologyToAdicQuotientLimit_closedPoint` —
  **Stacks 0EFR** in full over an arbitrary Noetherian local ring.

## Implementation notes

The descent is the universal property of the two completions. Restriction of scalars
`res : D(B) ⟶ D(A)` carries derived `IB`-complete objects to derived `I`-complete ones and is an
equivalence between those subcategories, which is Stacks 0925
(`CompleteRestrictScalarsEquivalence.restrictScalars_equivalence_derivedComplete`). The missing
step — that `res` is also bijective on morphisms from `L` to a derived complete object, for `L`
with `IB`-power-torsion cohomology, where `L` itself is not complete — comes from the derived
extension–restriction adjunction together with invertibility of its counit at `L`, and that
invertibility is Stacks 05E9 read in the derived category: the unit is invertible at every object
with `I`-power-torsion cohomology by
`Dualizing.PowerTorsionBaseChange.mapDerivedAdjunction_unit_isIso` applied to
`Dualizing.PowerTorsionBaseChange.extendRestrictScalars_unit_isIso_of_powerTorsion`, and the
triangle identity then inverts the counit after restriction of scalars, which reflects
isomorphisms.

So `res(L^∧)`, with the restriction of the completion unit of `L`, has the universal property of
the derived `I`-adic completion of `res L`; uniqueness of reflections identifies it with
`(res L)^∧` over the unit, and the identification is what transports invertibility on cohomology.

For Stacks 0EFR the object `L` is `RΓ_{𝔪'}(M')`, whose cohomology is `𝔪'`-power torsion and
hence `I'`-power torsion because `I ⊆ 𝔪`. The identification of `res L` with `RΓ_𝔪(M)` is the
first sentence of the source's proof: the unit of the adjunction at `RΓ_𝔪(M)` is invertible — the
same Stacks 05E9 input, local cohomology at `𝔪` being `I`-power torsion — and Stacks 0ALZ
(`Stacks.LocalCohomology.localCohomologyBaseChangeIso`) moves derived extension of scalars past
`RΓ`, while `𝔪 A' = 𝔪'` is part (G) of Stacks 0EFV
(`Stacks.Algebraization.BootstrapSituation.map_maximalIdeal_adicCompletion`).

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0925](https://stacks.math.columbia.edu/tag/0925)
* [Stacks Project, Tag 0924](https://stacks.math.columbia.edu/tag/0924)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
* [Stacks Project, Tag 0DXJ](https://stacks.math.columbia.edu/tag/0DXJ)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### Generic lemmas -/

section Generic

/-- Cohomology of the image of a morphism of the derived category under an exact additive functor
is invertible exactly when the functor applied to the cohomology of the morphism is. -/
private theorem isIso_homology_map_mapDerived_iff {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : DerivedCategory C} (f : X ⟶ Y) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f)) ↔
      IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) := by
  have e := StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n
  have hnat := e.hom.naturality f
  simp only [Functor.comp_map] at hnat
  rw [← isIso_comp_right_iff _ (e.hom.app Y), hnat, isIso_comp_left_iff]

/-- An exact additive functor which reflects isomorphisms of objects reflects isomorphisms in the
derived category, cohomology being computed before or after it indifferently. -/
private theorem isIso_of_isIso_mapDerived {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have := (isIso_homology_map_mapDerived_iff F f n).1 inferInstance
  exact isIso_of_reflects_iso _ F

/-- Two objects universal under `X` among a class of targets containing both are isomorphic
under `X`. This is the dual of `Stacks.LocalCohomology.exists_iso_over_of_universal`. -/
private theorem exists_iso_under_of_universal {C : Type*} [Category C] {X Y Y' : C}
    (c : X ⟶ Y) (c' : X ⟶ Y')
    (h1 : Function.Bijective (fun g : Y ⟶ Y' => c ≫ g))
    (h2 : Function.Bijective (fun g : Y' ⟶ Y => c' ≫ g))
    (h3 : Function.Injective (fun g : Y ⟶ Y => c ≫ g))
    (h4 : Function.Injective (fun g : Y' ⟶ Y' => c' ≫ g)) :
    ∃ e : Y ≅ Y', c ≫ e.hom = c' := by
  obtain ⟨p, hp⟩ := h1.2 c'
  obtain ⟨q, hq⟩ := h2.2 c
  change c ≫ p = c' at hp
  change c' ≫ q = c at hq
  refine ⟨⟨p, q, ?_, ?_⟩, hp⟩
  · apply h3
    show c ≫ p ≫ q = c ≫ 𝟙 Y
    rw [← Category.assoc, hp, hq, Category.comp_id]
  · apply h4
    show c' ≫ q ≫ p = c' ≫ 𝟙 Y'
    rw [← Category.assoc, hq, hp, Category.comp_id]

/-- Invertibility of the image of a unit under a functor transfers along an isomorphism of the
source object. -/
private theorem isIso_map_unit_app_of_iso {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) (F : C ⥤ C) (η : 𝟭 C ⟶ F) {X Y : C} (e : X ≅ Y)
    (h : IsIso (H.map (η.app Y))) : IsIso (H.map (η.app X)) := by
  have hnat : η.app X ≫ F.map e.hom = e.hom ≫ η.app Y := by
    simpa only [Functor.id_map] using (η.naturality e.hom).symm
  have h1 : IsIso (H.map (e.hom ≫ η.app Y)) := by
    rw [H.map_comp]
    have := h
    have : IsIso (H.map e.hom) := inferInstance
    infer_instance
  rw [← hnat, H.map_comp] at h1
  have h2 : IsIso (H.map (F.map e.hom)) := inferInstance
  exact IsIso.of_isIso_comp_right (H.map (η.app X)) (H.map (F.map e.hom))

/-- If `f ∘ g = f' ∘ g'` with `g`, `f'`, `g'` bijective, then `f` is bijective. -/
private theorem bijective_of_comp_eq {α β γ δ : Type*} {f : β → γ} {g : α → β} {f' : δ → γ}
    {g' : α → δ} (hg : Function.Bijective g) (hf' : Function.Bijective f')
    (hg' : Function.Bijective g') (h : ∀ x, f (g x) = f' (g' x)) : Function.Bijective f := by
  rw [← Function.Bijective.of_comp_iff f hg, show f ∘ g = f' ∘ g' from funext h]
  exact hf'.comp hg'

/-- Bijectivity of precomposition transfers along an isomorphism of the target. -/
private theorem bijective_comp_of_iso_target {C : Type*} [Category C] {X Y Z Z' : C}
    (c : X ⟶ Y) (e : Z ≅ Z') (h : Function.Bijective (fun g : Y ⟶ Z => c ≫ g)) :
    Function.Bijective (fun g : Y ⟶ Z' => c ≫ g) := by
  have hr (W : C) : Function.Bijective (fun g : W ⟶ Z => g ≫ e.hom) :=
    ⟨fun x y hxy => (cancel_mono e.hom).1 hxy, fun z => ⟨z ≫ e.inv, by simp⟩⟩
  exact bijective_of_comp_eq (hr Y) (hr X) h fun g => by simp

end Generic

/-! ### Derived extension and restriction of scalars along a flat map, isomorphic mod `I` -/

section FlatModIdeal

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Derived restriction of scalars `D(B) ⥤ D(A)`. -/
public abbrev derivedRestrictScalarsFunctor :
    DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars.{u} (algebraMap A B)).mapDerivedCategory

/-- Derived extension of scalars `D(A) ⥤ D(B)`. -/
public abbrev derivedExtendScalarsFunctor :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor

/-- The adjunction of Stacks 0GMT between derived extension and derived restriction of
scalars. -/
public abbrev derivedExtendRestrictAdjunction :
    derivedExtendScalarsFunctor A B ⊣ derivedRestrictScalarsFunctor A B :=
  Stacks.LocalCohomology.derivedExtensionRestrictAdjunction.{u, u, u} (algebraMap A B)

variable {A B}

/-- **Stacks 05E9 in the derived category.** For a flat `A → B` inducing an isomorphism modulo a
finitely generated ideal `I`, the unit of the derived extension–restriction adjunction is
invertible at every object of `D(A)` whose cohomology is `I`-power torsion. -/
public theorem isIso_derivedExtensionUnit_of_derivedPowerTorsion (I : Ideal A) (hI : I.FG)
    (hflat : Module.Flat A B)
    (hquot : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map))
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : Dualizing.derivedPowerTorsionProperty A I hI X) :
    IsIso ((derivedExtendRestrictAdjunction A B).unit.app X) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    Dualizing.PowerTorsionBaseChange.preservesFiniteLimits_extendScalars_of_flat.{u, u, u}
      A B hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    ModuleCat.extendScalars_preservesFiniteColimits.{u, u, u} (algebraMap A B)
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).Additive :=
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).additive_of_preserves_binary_products
  set adjM := ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B) with hadjM
  have h1 : IsIso (adjM.mapDerivedCategory.unit.app X) :=
    Dualizing.PowerTorsionBaseChange.mapDerivedAdjunction_unit_isIso adjM X fun i =>
      Dualizing.PowerTorsionBaseChange.extendRestrictScalars_unit_isIso_of_powerTorsion.{u, u, u}
        A B I hflat hquot _ (hX i)
  have htr := Adjunction.unit_leftAdjointUniq_hom_app adjM.mapDerivedCategory
    (derivedExtendRestrictAdjunction A B) X
  rw [← htr]
  have h2 : IsIso ((derivedRestrictScalarsFunctor A B).map
      ((Adjunction.leftAdjointUniq adjM.mapDerivedCategory
        (derivedExtendRestrictAdjunction A B)).hom.app X)) :=
    inferInstance
  exact IsIso.comp_isIso' h1 h2

/-- The counit of the derived extension–restriction adjunction is invertible at an object of
`D(B)` whose cohomology is `IB`-power torsion. Restriction of scalars inverts it by the triangle
identity, the unit being invertible at the restriction, and restriction of scalars reflects
isomorphisms. -/
public theorem isIso_derivedExtensionCounit_of_derivedPowerTorsion (I : Ideal A) (hI : I.FG)
    (hflat : Module.Flat A B)
    (hquot : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map))
    (L : DerivedCategory (ModuleCat.{u} B))
    (hL : Dualizing.derivedPowerTorsionProperty B (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) L) :
    IsIso ((derivedExtendRestrictAdjunction A B).counit.app L) := by
  have hres : Dualizing.derivedPowerTorsionProperty A I hI
      ((derivedRestrictScalarsFunctor A B).obj L) :=
    Stacks.LocalCohomology.derivedPowerTorsionProperty_restrictScalars.{u, u, u}
      (algebraMap A B) I hI L hL
  have hunit : IsIso ((derivedExtendRestrictAdjunction A B).unit.app
      ((derivedRestrictScalarsFunctor A B).obj L)) :=
    isIso_derivedExtensionUnit_of_derivedPowerTorsion I hI hflat hquot _ hres
  have hmap : IsIso ((derivedRestrictScalarsFunctor A B).map
      ((derivedExtendRestrictAdjunction A B).counit.app L)) :=
    IsIso.of_isIso_fac_left ((derivedExtendRestrictAdjunction A B).right_triangle_components L)
  exact isIso_of_isIso_mapDerived (ModuleCat.restrictScalars.{u} (algebraMap A B))
    ((derivedExtendRestrictAdjunction A B).counit.app L) hmap

/-- Restriction of scalars is bijective on morphisms out of an object of `D(B)` whose cohomology
is `IB`-power torsion. Composing with the counit, which is invertible there, turns it into the
adjunction bijection. -/
public theorem bijective_restrictScalars_map_of_derivedPowerTorsion (I : Ideal A) (hI : I.FG)
    (hflat : Module.Flat A B)
    (hquot : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map))
    (L : DerivedCategory (ModuleCat.{u} B))
    (hL : Dualizing.derivedPowerTorsionProperty B (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) L)
    (E : DerivedCategory (ModuleCat.{u} B)) :
    Function.Bijective (fun k : L ⟶ E => (derivedRestrictScalarsFunctor A B).map k) := by
  have hcounit : IsIso ((derivedExtendRestrictAdjunction A B).counit.app L) :=
    isIso_derivedExtensionCounit_of_derivedPowerTorsion I hI hflat hquot L hL
  have hpre : Function.Bijective
      (fun k : L ⟶ E => (derivedExtendRestrictAdjunction A B).counit.app L ≫ k) := by
    have := hcounit
    exact ⟨fun x y hxy => (cancel_epi ((derivedExtendRestrictAdjunction A B).counit.app L)).1 hxy,
      fun z => ⟨inv ((derivedExtendRestrictAdjunction A B).counit.app L) ≫ z, by simp⟩⟩
  have hkey : ∀ k : L ⟶ E, (derivedRestrictScalarsFunctor A B).map k =
      ((derivedExtendRestrictAdjunction A B).homEquiv ((derivedRestrictScalarsFunctor A B).obj L) E)
        ((derivedExtendRestrictAdjunction A B).counit.app L ≫ k) := by
    intro k
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      (derivedExtendRestrictAdjunction A B).right_triangle_components L, Category.id_comp]
  refine ⟨fun k₁ k₂ h => hpre.1 ?_, fun g => ?_⟩
  · refine ((derivedExtendRestrictAdjunction A B).homEquiv
      ((derivedRestrictScalarsFunctor A B).obj L) E).injective ?_
    rw [← hkey k₁, ← hkey k₂]
    exact h
  · obtain ⟨m, hm⟩ := hpre.2 (((derivedExtendRestrictAdjunction A B).homEquiv
      ((derivedRestrictScalarsFunctor A B).obj L) E).symm g)
    refine ⟨m, ?_⟩
    change (derivedExtendRestrictAdjunction A B).counit.app L ≫ m = _ at hm
    show (derivedRestrictScalarsFunctor A B).map m = g
    rw [hkey m, hm, Equiv.apply_symm_apply]


/-! ### Stacks 0925 unpacked -/

/-- **Stacks 0925, unpacked.** Restriction of scalars is bijective on morphisms between derived
complete objects, and every derived `I`-complete object of `D(A)` is isomorphic to the
restriction of scalars of a derived `IB`-complete object of `D(B)`. -/
private theorem restrictScalars_derivedComplete_bijective_and_essSurj
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map)) :
    (∀ X' Y' : DerivedCategory (ModuleCat.{u} B),
        IsDerivedComplete (I.map (algebraMap A B)) X' →
        IsDerivedComplete (I.map (algebraMap A B)) Y' →
        Function.Bijective (fun k : X' ⟶ Y' => (derivedRestrictScalarsFunctor A B).map k)) ∧
      ∀ E : DerivedCategory (ModuleCat.{u} A), IsDerivedComplete I E →
        ∃ E' : DerivedCategory (ModuleCat.{u} B),
          IsDerivedComplete (I.map (algebraMap A B)) E' ∧
            Nonempty ((derivedRestrictScalarsFunctor A B).obj E' ≅ E) := by
  obtain ⟨hprodA, hprodB, hres, hequiv⟩ :=
    CompleteRestrictScalarsEquivalence.restrictScalars_equivalence_derivedComplete.{u}
      A B I hI hflat hquot
  set completeA : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K ↦ IsDerivedComplete I K with hcA
  set completeB : ObjectProperty (DerivedCategory (ModuleCat.{u} B)) :=
    fun K ↦ IsDerivedComplete (I.map (algebraMap A B)) K with hcB
  set T := completeA.lift (completeB.ι ⋙ derivedRestrictScalarsFunctor A B)
    (fun K ↦ hres K) with hT
  have := hequiv
  refine ⟨fun X' Y' hX' hY' => ?_, fun E hE => ?_⟩
  · have hu : Function.Bijective
        (ObjectProperty.homMk (X := (⟨X', hX'⟩ : completeB.FullSubcategory))
          (Y := ⟨Y', hY'⟩)) :=
      ⟨fun a b hab => congrArg InducedCategory.Hom.hom hab,
        ObjectProperty.homMk_surjective⟩
    have hv : Function.Bijective
        (fun f : (⟨X', hX'⟩ : completeB.FullSubcategory) ⟶ ⟨Y', hY'⟩ => T.map f) :=
      ⟨T.map_injective, T.map_surjective⟩
    have hw : Function.Bijective
        (fun f : T.obj ⟨X', hX'⟩ ⟶ T.obj ⟨Y', hY'⟩ => f.hom) :=
      ⟨fun a b hab => ObjectProperty.hom_ext _ hab,
        fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
    exact (hw.comp hv).comp hu
  · exact ⟨(T.objPreimage ⟨E, hE⟩).obj, (T.objPreimage ⟨E, hE⟩).property,
      ⟨completeA.ι.mapIso (T.objObjPreimageIso ⟨E, hE⟩)⟩⟩

/-! ### Descent of the derived completion -/

/-- **The derived completion descends along restriction of scalars.** For a flat `A → B`
inducing an isomorphism modulo a finitely generated ideal `I`, and an object `L` of `D(B)` whose
cohomology is `IB`-power torsion, the derived `I`-adic completion of the restriction of scalars
of `L` is the restriction of scalars of the derived `IB`-adic completion of `L`, by an
isomorphism compatible with the two completion units.

Both objects are derived `I`-complete, by Stacks 0924 for the second, and both receive `res L`
universally among derived `I`-complete objects: the first by definition, the second because
restriction of scalars is bijective on morphisms out of `L` and on morphisms between complete
objects. Uniqueness of reflections gives the isomorphism over the units. -/
public theorem exists_iso_adicCompletion_restrictScalars (I : Ideal A) (hI : I.FG)
    (hflat : Module.Flat A B)
    (hquot : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map))
    (L : DerivedCategory (ModuleCat.{u} B))
    (hL : Dualizing.derivedPowerTorsionProperty B (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) L) :
    ∃ e : (adicCompletionFunctor A I hI).obj ((derivedRestrictScalarsFunctor A B).obj L) ≅
        (derivedRestrictScalarsFunctor A B).obj
          ((adicCompletionFunctor B (I.map (algebraMap A B))
            (hI.map (algebraMap A B))).obj L),
      (adicCompletionUnit A I hI).app ((derivedRestrictScalarsFunctor A B).obj L) ≫ e.hom =
        (derivedRestrictScalarsFunctor A B).map
          ((adicCompletionUnit B (I.map (algebraMap A B))
            (hI.map (algebraMap A B))).app L) := by
  obtain ⟨hff, hess⟩ :=
    restrictScalars_derivedComplete_bijective_and_essSurj I hI hflat hquot
  have hcompA : IsDerivedComplete I
      ((adicCompletionFunctor A I hI).obj ((derivedRestrictScalarsFunctor A B).obj L)) :=
    ((Dualizing.derivedCompletion A I hI).obj
      ((derivedRestrictScalarsFunctor A B).obj L)).property
  have hcompB' : IsDerivedComplete (I.map (algebraMap A B))
      ((adicCompletionFunctor B (I.map (algebraMap A B))
        (hI.map (algebraMap A B))).obj L) :=
    ((Dualizing.derivedCompletion B (I.map (algebraMap A B))
      (hI.map (algebraMap A B))).obj L).property
  have hcompB : IsDerivedComplete I
      ((derivedRestrictScalarsFunctor A B).obj
        ((adicCompletionFunctor B (I.map (algebraMap A B))
          (hI.map (algebraMap A B))).obj L)) :=
    (isDerivedComplete_restrictScalars_iff A B (algebraMap A B) I _).2 hcompB'
  have hUB : ∀ E : DerivedCategory (ModuleCat.{u} A), IsDerivedComplete I E →
      Function.Bijective (fun g : (derivedRestrictScalarsFunctor A B).obj
          ((adicCompletionFunctor B (I.map (algebraMap A B))
            (hI.map (algebraMap A B))).obj L) ⟶ E =>
        (derivedRestrictScalarsFunctor A B).map
          ((adicCompletionUnit B (I.map (algebraMap A B))
            (hI.map (algebraMap A B))).app L) ≫ g) := by
    intro E hE
    obtain ⟨E', hE', ⟨eE⟩⟩ := hess E hE
    refine bijective_comp_of_iso_target _ eE ?_
    have h1 := hff ((adicCompletionFunctor B (I.map (algebraMap A B))
      (hI.map (algebraMap A B))).obj L) E' hcompB' hE'
    have h2 := bijective_restrictScalars_map_of_derivedPowerTorsion I hI hflat hquot L hL E'
    have h3 := completionUnit_comp_bijective (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) L E' hE'
    exact bijective_of_comp_eq h1 h2 h3 fun k => by simp
  exact exists_iso_under_of_universal _ _
    (completionUnit_comp_bijective I hI _ _ hcompB)
    (hUB _ hcompA)
    (completionUnit_comp_bijective I hI _ _ hcompA).1
    (hUB _ hcompB).1

/-- **Invertibility of the derived completion unit on cohomology descends along restriction of
scalars.** For an object `L` of `D(B)` with `IB`-power-torsion cohomology, if the derived
`IB`-adic completion unit of `L` is invertible on cohomology in degree `i`, then so is the
derived `I`-adic completion unit of the restriction of scalars of `L`. -/
public theorem isIso_homology_adicCompletionUnit_restrictScalars (I : Ideal A) (hI : I.FG)
    (hflat : Module.Flat A B)
    (hquot : Function.Bijective (Ideal.quotientMap (I.map (algebraMap A B))
      (algebraMap A B) Ideal.le_comap_map))
    (L : DerivedCategory (ModuleCat.{u} B))
    (hL : Dualizing.derivedPowerTorsionProperty B (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) L)
    (i : ℤ)
    (h' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      ((adicCompletionUnit B (I.map (algebraMap A B))
        (hI.map (algebraMap A B))).app L))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app ((derivedRestrictScalarsFunctor A B).obj L))) := by
  obtain ⟨e, he⟩ := exists_iso_adicCompletion_restrictScalars I hI hflat hquot L hL
  have hres : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((derivedRestrictScalarsFunctor A B).map
        ((adicCompletionUnit B (I.map (algebraMap A B))
          (hI.map (algebraMap A B))).app L))) := by
    rw [derivedRestrictScalarsFunctor, isIso_homology_map_mapDerived_iff]
    infer_instance
  have hA : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app ((derivedRestrictScalarsFunctor A B).obj L) ≫ e.hom)) := by
    rw [he]
    exact hres
  rw [Functor.map_comp] at hA
  have he' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map e.hom) :=
    inferInstance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map e.hom)



end FlatModIdeal

/-! ### Local cohomology at the closed point over the adic completion -/

section LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The first sentence of the proof of Stacks 0EFR.** For an ideal `I` of a Noetherian ring
contained in an ideal `J` and a finite module `M`, local cohomology `RΓ_J(M)` is the restriction
of scalars of local cohomology `RΓ_{J A'}(M')` over the `I`-adic completion `A'`, where
`M' = M ⊗_A A'` is the `I`-adic completion of `M`.

Local cohomology at `J` has `J`-power-torsion cohomology, hence `I`-power-torsion cohomology
because `I ⊆ J`, so the unit of the derived extension–restriction adjunction is invertible there
by Stacks 05E9 read in the derived category. Stacks 0ALZ then moves derived extension of scalars
past local cohomology, and `A' ⊗_A M = M^∧` identifies the coefficients. -/
public theorem nonempty_iso_localCohomology_restrictScalars_adicCompletion
    (I J : Ideal A) (hIJ : I ≤ J) (M : ModuleCat.{u} A) [Module.Finite A M]
    (J' : Ideal (AdicCompletion I A))
    (hJ' : J.map (algebraMap A (AdicCompletion I A)) = J') :
    Nonempty ((Stacks.LocalCohomology.localCohomologyDerived A J
          (Ideal.fg_of_isNoetherianRing _)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (derivedRestrictScalarsFunctor A (AdicCompletion I A)).obj
        ((Stacks.LocalCohomology.localCohomologyDerived (AdicCompletion I A)
            J' (Ideal.fg_of_isNoetherianRing _)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (AdicCompletion I A)) 0).obj
            (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M))))) := by
  subst hJ'
  have hflat : Module.Flat A (AdicCompletion I A) := AdicCompletion.flat_of_isNoetherian I
  have hRflat : (algebraMap A (AdicCompletion I A)).Flat :=
    RingHom.flat_algebraMap_iff.mpr hflat
  have hquot := AdicCompletion.quotientMap_bijective I (Ideal.fg_of_isNoetherianRing I)
  have htor : Dualizing.derivedPowerTorsionProperty A I (Ideal.fg_of_isNoetherianRing I)
      ((Stacks.LocalCohomology.localCohomologyDerived A J
        (Ideal.fg_of_isNoetherianRing _)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
    intro i
    exact Dualizing.TorsionCounit.isIPowerTorsion_of_le hIJ
      (((Dualizing.localCohomologyFunctor A J (Ideal.fg_of_isNoetherianRing _)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).property i)
  have hu := isIso_derivedExtensionUnit_of_derivedPowerTorsion I
    (Ideal.fg_of_isNoetherianRing I) hflat hquot _ htor
  let e3 : (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A))).obj M ≅
      ModuleCat.of (AdicCompletion I A) (AdicCompletion I M) :=
    ((IPowerTorsion.tensorModuleCatEquiv.{u, u, u} (R := A)
        (S := AdicCompletion I A) M).symm.trans
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M)).toModuleIso
  let e4 : (derivedExtendScalarsFunctor A (AdicCompletion I A)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (AdicCompletion I A)) 0).obj
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M)) :=
    derivedExtensionScalarsSingleIso.{u, u, u} (algebraMap A (AdicCompletion I A)) hRflat M ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (AdicCompletion I A)) 0).mapIso e3
  let e1 := (Stacks.LocalCohomology.localCohomologyBaseChangeIso.{u, u, u}
    (algebraMap A (AdicCompletion I A)) J (Ideal.fg_of_isNoetherianRing _)).app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
  exact ⟨asIso ((derivedExtendRestrictAdjunction A (AdicCompletion I A)).unit.app
      ((Stacks.LocalCohomology.localCohomologyDerived A J
        (Ideal.fg_of_isNoetherianRing _)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) ≪≫
    (derivedRestrictScalarsFunctor A (AdicCompletion I A)).mapIso
    (e1 ≪≫ (Stacks.LocalCohomology.localCohomologyDerived (AdicCompletion I A)
      (J.map (algebraMap A (AdicCompletion I A)))
      (Ideal.fg_of_isNoetherianRing _)).mapIso e4)⟩

end LocalCohomology

/-! ### Stacks 0EFR over an arbitrary Noetherian local ring -/

section Bootstrap

/-- The arrow of Stacks 0EFL at `J' = J` is the derived `I`-adic completion unit followed by an
isomorphism, so it is invertible on cohomology exactly when the unit is. -/
private theorem isIso_homology_toCompleted_iff
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyToCompletedLocalCohomology A I J J hI hJ hJ M rfl)) ↔
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app
        ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) := by
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (completedLocalCohomologyShrinkIso A I J J hI hJ hJ M rfl).hom) := inferInstance
  rw [show localCohomologyToCompletedLocalCohomology A I J J hI hJ hJ M rfl =
      Dualizing.completedLocalCohomologyUnit A I J hI hJ M ≫
        (completedLocalCohomologyShrinkIso A I J J hI hJ hJ M rfl).hom from rfl,
    Functor.map_comp, isIso_comp_right_iff]
  exact Iff.rfl

variable (S : BootstrapSituation.{u, u, u})

/-- **The first display of the proof of Stacks 0EFR, over `A` itself.** In the bootstrap
situation of Stacks 0EFU with `A` local and `T = {𝔪}`, the canonical map
`RΓ_𝔪(M) ⟶ RΓ_𝔪(M)^∧` is an isomorphism on cohomology in degrees `i ≤ s`, with no completeness
assumption on `A`.

This is the third paragraph of the source's proof. Stacks 0DXP gives the display over the
`I`-adic completion `A'`, part (G) of Stacks 0EFV making `A', I', M'` a bootstrap situation whose
locus is the closed point of `A'`; the display is then carried back down to `A` by
`Stacks.Algebraization.isIso_homology_adicCompletionUnit_restrictScalars`, along the
identification `RΓ_𝔪(M) = RΓ_{𝔪'}(M')` of
`Stacks.Algebraization.nonempty_iso_localCohomology_restrictScalars_adicCompletion`. -/
public theorem isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i).map
      (localCohomologyToCompletedLocalCohomology S.A S.I (maximalIdeal S.A) (maximalIdeal S.A)
        S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _)
        (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) rfl)) := by
  let hlocA' : IsLocalRing (AdicCompletion S.I S.A) :=
    BootstrapSituation.isLocalRing_adicCompletion_self S hT
  have hIm : S.I ≤ maximalIdeal S.A :=
    S.subset_adicLocus (by rw [hT]; exact Set.mem_singleton _)
  have hmap : (maximalIdeal S.A).map (algebraMap S.A (AdicCompletion S.I S.A)) =
      maximalIdeal (AdicCompletion S.I S.A) :=
    BootstrapSituation.map_maximalIdeal_adicCompletion S hT
  have hA'unit := (isIso_homology_toCompleted_iff (AdicCompletion S.I S.A)
    (S.I.map (algebraMap S.A (AdicCompletion S.I S.A)))
    (maximalIdeal (AdicCompletion S.I S.A)) (Ideal.fg_of_isNoetherianRing _)
    (Ideal.fg_of_isNoetherianRing _)
    (ModuleCat.of (AdicCompletion S.I S.A) (AdicCompletion S.I S.M)) i).1
    (isIso_homology_localCohomologyToCompletedLocalCohomology_adicCompletion S hT i hi)
  have htor : Dualizing.derivedPowerTorsionProperty (AdicCompletion S.I S.A)
      (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) (Ideal.fg_of_isNoetherianRing _)
      ((Stacks.LocalCohomology.localCohomologyDerived (AdicCompletion S.I S.A)
        (maximalIdeal (AdicCompletion S.I S.A)) (Ideal.fg_of_isNoetherianRing _)).obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (AdicCompletion S.I S.A)) 0).obj
          (ModuleCat.of (AdicCompletion S.I S.A) (AdicCompletion S.I S.M)))) := by
    intro j
    refine Dualizing.TorsionCounit.isIPowerTorsion_of_le ?_
      (((Dualizing.localCohomologyFunctor (AdicCompletion S.I S.A)
        (maximalIdeal (AdicCompletion S.I S.A)) (Ideal.fg_of_isNoetherianRing _)).obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (AdicCompletion S.I S.A)) 0).obj
          (ModuleCat.of (AdicCompletion S.I S.A) (AdicCompletion S.I S.M)))).property j)
    rw [← hmap]
    exact Ideal.map_mono hIm
  have hdesc := isIso_homology_adicCompletionUnit_restrictScalars S.I
    (Ideal.fg_of_isNoetherianRing S.I) (AdicCompletion.flat_of_isNoetherian S.I)
    (AdicCompletion.quotientMap_bijective S.I (Ideal.fg_of_isNoetherianRing S.I)) _ htor i
    hA'unit
  obtain ⟨e⟩ := nonempty_iso_localCohomology_restrictScalars_adicCompletion S.I
    (maximalIdeal S.A) hIm (ModuleCat.of S.A S.M)
    (maximalIdeal (AdicCompletion S.I S.A)) hmap
  refine (isIso_homology_toCompleted_iff S.A S.I (maximalIdeal S.A)
    S.I.fg_of_isNoetherianRing (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i).2 ?_
  exact isIso_map_unit_app_of_iso (DerivedCategory.homologyFunctor (ModuleCat.{u} S.A) i)
    (adicCompletionFunctor S.A S.I S.I.fg_of_isNoetherianRing)
    (adicCompletionUnit S.A S.I S.I.fg_of_isNoetherianRing) e hdesc

/-- **Stacks 0EFR.** In the bootstrap situation of Stacks 0EFU with `A` local and
`T = {𝔪}`, the map `Hⁱ_𝔪(M) ⟶ lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s`, and a single power
of `I` annihilates these modules. Nothing is assumed about `A` beyond Situation 0EFU and the
locality of the locus; in particular `A` need not be `I`-adically complete.

The isomorphism is the composite of the two displays of the source's proof. The first,
`Hⁱ_𝔪(M) ≅ Hⁱ(RΓ_𝔪(M)^∧)`, is
`Stacks.Algebraization.isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint`,
which obtains it over the `I`-adic completion from Stacks 0DXP and Stacks 0EFQ and descends it;
the second, `Hⁱ(RΓ_𝔪(M)^∧) ≅ lim Hⁱ_𝔪(M/IⁿM)`, is Stacks 0DXJ. The annihilation assertion is
`Stacks.Algebraization.exists_pow_le_annihilator_localCohomologyModule_of_eq_closedPoint`, which
needs only Stacks 0EFQ over `A` itself. -/
@[stacks 0EFR "both assertions over A itself for every Noetherian local ring: in Situation 0EFU
with A local and T = {𝔪}, the map Hⁱ_𝔪(M) → lim Hⁱ_𝔪(M/IⁿM) is an isomorphism for i ≤ s and a
single power of I annihilates these modules"]
public theorem isIso_localCohomologyToAdicQuotientLimit_closedPoint
    [IsLocalRing S.A] (hT : S.T = {closedPoint S.A}) :
    (∀ i : ℤ, i ≤ S.s →
        IsIso (localCohomologyToAdicQuotientLimit S.A S.I (maximalIdeal S.A)
          (maximalIdeal S.A) (ModuleCat.of S.A S.M) rfl i)) ∧
      ∃ n : ℕ, ∀ i : ℤ, i ≤ S.s →
        S.I ^ n ≤ Module.annihilator S.A
          (Stacks.LocalCohomology.localCohomologyModule S.A (maximalIdeal S.A)
            (Ideal.fg_of_isNoetherianRing _) (ModuleCat.of S.A S.M) i) :=
  isIso_localCohomologyToAdicQuotientLimit_and_exists_pow_le_annihilator S hT
    (isIso_homology_localCohomologyToCompletedLocalCohomology_closedPoint S hT)

end Bootstrap

end Stacks.Algebraization

end
