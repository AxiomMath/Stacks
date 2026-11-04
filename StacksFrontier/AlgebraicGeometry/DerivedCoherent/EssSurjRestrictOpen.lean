module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExtendBoundedComplex
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.RestrictOpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to an open subscheme is essentially surjective on `D^b_Coh`

Let `X` be a Noetherian scheme and `U ⊆ X` an open subscheme. Every object of `D^b_Coh(𝒪_U)` is
the restriction of an object of `D^b_Coh(𝒪_X)`.

The proof replaces the given object of `D^b_Coh(𝒪_U)` by a bounded complex of coherent
`𝒪_U`-modules, using the equivalence `D^b(Coh(𝒪_U)) ≌ D^b_Coh(𝒪_U)` of [Stacks, Tag 0FDB] and a
strict representative of the resulting object of `D^b(Coh(𝒪_U))`; extends that complex to a
bounded complex of coherent `𝒪_X`-modules; and reads the extension back in `D^b_Coh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.essSurj_coherentDerivedBoundedRestrict`: **[Stacks, Tag 0G48]**.

## References

* [Stacks Project, Tag 0G48](https://stacks.math.columbia.edu/tag/0G48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- An open subscheme of a Noetherian scheme is Noetherian: it is locally Noetherian because the
inclusion is an open immersion, and quasi-compact because a subspace of a Noetherian space is a
Noetherian space. -/
@[ega "I 6.1.4" "special case"]
theorem isNoetherian_opens_toScheme {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) :
    IsNoetherian U.toScheme :=
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : TopologicalSpace.NoetherianSpace (U.toScheme : Type u) :=
    TopologicalSpace.NoetherianSpace.set (U : Set X)
  have : CompactSpace (U.toScheme : Type u) := inferInstance
  { }

/-- A complex of coherent modules, read as a complex in `Coh(𝒪_X)`. -/
def coherentLiftComplex {X : Scheme.{u}}
    (𝒢 : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (h : ∀ i, (𝒢.X i).IsCoherent) :
    CochainComplex (SheafOfModules.CoherentModules X.ringCatSheaf) ℤ where
  X i := ⟨𝒢.X i, h i⟩
  d i j := ObjectProperty.homMk (𝒢.d i j)
  shape i j hij := ObjectProperty.hom_ext _ (𝒢.shape i j hij)
  d_comp_d' i j k hij hjk := ObjectProperty.hom_ext _ (𝒢.d_comp_d' i j k hij hjk)

/-- The inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` returns a lifted complex unchanged. -/
theorem mapHomologicalComplex_coherentLiftComplex {X : Scheme.{u}}
    (𝒢 : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (h : ∀ i, (𝒢.X i).IsCoherent) :
    ((coherentInModules X).ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (coherentLiftComplex 𝒢 h) = 𝒢 :=
  rfl

/-- A term of a lifted complex is zero as soon as the corresponding term was. -/
theorem isZero_coherentLiftComplex_X {X : Scheme.{u}}
    (𝒢 : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
    (h : ∀ i, (𝒢.X i).IsCoherent) (i : ℤ) (hi : IsZero (𝒢.X i)) :
    IsZero ((coherentLiftComplex 𝒢 h).X i) :=
  (IsZero.iff_id_eq_zero _).2 (ObjectProperty.hom_ext _ ((IsZero.iff_id_eq_zero _).1 hi))

/-- If a complex is strictly `≥ a` and strictly `≤ b` and the terms of another complex are zero
whenever those of the first are, then the other complex is strictly `≥ a` and strictly `≤ b`. -/
private theorem isStrictlyGE_and_isStrictlyLE_of_isZero_X
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {K : CochainComplex C ℤ} {L : CochainComplex D ℤ} (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] (h : ∀ i, IsZero (K.X i) → IsZero (L.X i)) :
    L.IsStrictlyGE a ∧ L.IsStrictlyLE b :=
  ⟨(CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => h i (K.isZero_of_isStrictlyGE a i hi),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => h i (K.isZero_of_isStrictlyLE b i hi)⟩

/-- **[Stacks, Tag 0G48].** On a Noetherian scheme, restriction to an open subscheme is
essentially surjective as a functor `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_U)`: every bounded complex of
`𝒪_U`-modules with coherent cohomology is the restriction of one on `X`. -/
@[stacks 0G48]
theorem essSurj_coherentDerivedBoundedRestrict {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens) :
    (coherentDerivedBoundedRestrict U).EssSurj where
  mem_essImage K := by
    have hUN : IsNoetherian U.toScheme := isNoetherian_opens_toScheme U
    -- replace `K` by an object of `D^b(Coh(𝒪_U))`
    let Y := (coherentToModulesDerivedBounded U.toScheme).objPreimage K
    have eY : ((coherentToModulesDerivedBounded U.toScheme).obj Y).obj ≅ K.obj :=
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules U.toScheme)).ι.mapIso
        ((coherentToModulesDerivedBounded U.toScheme).objObjPreimageIso K)
    obtain ⟨a, ha⟩ := Y.property.1
    obtain ⟨b, hb⟩ := Y.property.2
    -- a strict representative, whose terms are coherent by construction
    obtain ⟨ℱ', hGE', hLE', ⟨eF⟩⟩ :=
      DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE Y.obj a b
    let ℱ : CochainComplex U.toScheme.Modules ℤ :=
      ((coherentInModules U.toScheme).ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj ℱ'
    obtain ⟨hGE, hLE⟩ := isStrictlyGE_and_isStrictlyLE_of_isZero_X (L := ℱ) (K := ℱ') a b
      fun i => Functor.map_isZero (coherentInModules U.toScheme).ι
    -- extend the complex to `X`
    obtain ⟨𝒢, hGcoh, hGGE, hGLE, ⟨eG⟩⟩ :=
      Stacks.AlgebraicGeometry.ExtendBoundedComplex.exists_bounded_isCoherent_complex_restrict_iso
        U a b ℱ (fun i => (ℱ'.X i).property) hGE hLE
    obtain ⟨hGGE', hGLE'⟩ := isStrictlyGE_and_isStrictlyLE_of_isZero_X (K := 𝒢)
      (L := coherentLiftComplex 𝒢 hGcoh) a b (isZero_coherentLiftComplex_X 𝒢 hGcoh)
    -- read the extension in `D^b(Coh(𝒪_X))`, hence in `D^b_Coh(𝒪_X)`
    let E : DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) :=
      ⟨DerivedCategory.Q.obj (coherentLiftComplex 𝒢 hGcoh), ⟨a, inferInstance⟩,
        ⟨b, inferInstance⟩⟩
    refine ⟨(coherentToModulesDerivedBounded X).obj E, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    -- the chain of isomorphisms landing on `K`
    refine (Stacks.DerivedQCoh.modulesRestrict U).mapDerivedCategory.mapIso
      ((coherentInModules X).ι.mapDerivedCategoryFactors.app
        (coherentLiftComplex 𝒢 hGcoh)) ≪≫ ?_
    dsimp only [Functor.comp_obj]
    rw [mapHomologicalComplex_coherentLiftComplex 𝒢 hGcoh]
    refine (Stacks.DerivedQCoh.modulesRestrict U).mapDerivedCategoryFactors.app 𝒢 ≪≫ ?_
    refine DerivedCategory.Q.mapIso eG ≪≫ ?_
    exact ((coherentInModules U.toScheme).ι.mapDerivedCategoryFactors.app ℱ').symm ≪≫
      (coherentInModules U.toScheme).ι.mapDerivedCategory.mapIso eF.symm ≪≫ eY

end AlgebraicGeometry

end
