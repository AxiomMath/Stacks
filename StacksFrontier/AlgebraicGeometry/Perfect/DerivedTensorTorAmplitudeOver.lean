module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOverSheaf
public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent

/-!
# Tor amplitude over the base of a derived tensor product with a flat complex

Let `f : X ⟶ S` be a morphism of schemes, `E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded
complex of `𝒪_X`-modules whose terms are flat over `S` and supported in a quasi-compact subset `Z`
of `X`. Then `E ⊗^L_{𝒪_X} 𝒢` has finite Tor dimension over `S`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoOfDerivedTensorProduct`: the
  stalk of `E ⊗^L F`, for any derived tensor product of [Stacks, Tag 06YU], is the canonical
  derived tensor product of the stalks.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_derivedTensor`:
  [Stacks, Tag 0B66] for objects of the derived category and an arbitrary ring map.
* `AlgebraicGeometry.hasTorAmplitudeCanonical_derivedStalk_derivedTensor`: the same at one stalk
  of a derived tensor product on a scheme, read over the base.
* `AlgebraicGeometry.hasTorAmplitudeOver_of_isFlatOver`: a bounded complex of modules flat over
  the base has Tor amplitude over the base in its range.
* `AlgebraicGeometry.exists_hasTorAmplitudeOver_derivedTensor`: `E ⊗^L 𝒢` has finite Tor
  dimension over `S`.

## References

* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 09U9](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.SheafOfModules.DerivedTensorStalk

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)]

/-- **The stalk of a derived tensor product is the derived tensor product of the stalks**, for
any derived tensor product `T` of [Stacks, Tag 06YU]: the isomorphism
`derivedTensorStalkIsoOfKFlat` on K-flat representatives of `E` and `F`. -/
def derivedTensorStalkIsoOfDerivedTensorProduct
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)
    (E F : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        ((T.tensor.obj E).obj F) ≅
      ((stalkDerivedTensor R x).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj E)).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj F) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
      (((T.tensor.obj _).mapIso (kFlatModelIso R F) ≪≫
          (T.tensor.mapIso (kFlatModelIso R E)).app F).symm ≪≫
        T.comparison _ _ (kFlat_kFlatModel R E) (kFlat_kFlatModel R F) ≪≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison _ _
          (kFlat_kFlatModel R E) (kFlat_kFlatModel R F)).symm) ≪≫
    (derivedTensorStalkIsoOfKFlat R x _ _ (kFlat_kFlatModel R E) (kFlat_kFlatModel R F)).symm ≪≫
    ((stalkDerivedTensor R x).mapIso
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
            (kFlatModelIso R E))).app _ ≪≫
    ((stalkDerivedTensor R x).obj _).mapIso
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
          (kFlatModelIso R F))

end Stacks.SheafOfModules.DerivedTensorStalk

namespace StacksDraft.TorAmplitude

open CochainComplex.DerivedTensor

/-- **[Stacks, Tag 0B66] for objects of the derived category and an arbitrary ring map.** If `K`
has Tor amplitude in `[a, b]` over `B` and `L`, read over `A` along `τ : A →+* B`, has Tor
amplitude in `[c, d]`, then `K ⊗^L_B L`, read over `A`, has Tor amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitudeCanonical_restrictScalars_derivedTensor {A B : Type u} [CommRing A]
    [CommRing B] (τ : A →+* B) (K L : DerivedCategory (ModuleCat.{u} B)) (a b c d : ℤ)
    (hK : HasTorAmplitudeCanonical B K a b)
    (hL : HasTorAmplitudeCanonical A ((ModuleCat.restrictScalars τ).mapDerivedCategory.obj L)
      c d) :
    HasTorAmplitudeCanonical A ((ModuleCat.restrictScalars τ).mapDerivedCategory.obj
      (((canonicalDerivedTensorProduct B).tensor.obj K).obj L)) (a + c) (b + d) := by
  let : Algebra A B := τ.toAlgebra
  have eK := DerivedCategory.Q.objObjPreimageIso K
  have eL := DerivedCategory.Q.objObjPreimageIso L
  have h := hasTorAmplitudeCanonical_derivedTensorProduct A B (DerivedCategory.Q.objPreimage K)
    (DerivedCategory.Q.objPreimage L) a b c d
    (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso eK.symm a b hK)
    (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((ModuleCat.restrictScalars τ).mapDerivedCategory.mapIso eL.symm) c d hL)
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars τ).mapDerivedCategory.mapIso
      ((((canonicalDerivedTensorProduct B).tensor.mapIso eK).app _) ≪≫
        ((canonicalDerivedTensorProduct B).tensor.obj K).mapIso eL)) _ _ h

/-- A zero object of the derived category has Tor amplitude in every interval. -/
theorem hasTorAmplitudeCanonical_of_isZero {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (hK : IsZero K) (a b : ℤ) :
    HasTorAmplitudeCanonical R K a b := by
  have hz : ∀ i : ℤ, IsZero
      ((HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
    fun i => Limits.isZero_zero _
  refine (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).2
    ⟨HomologicalComplex.zero, fun i => ?_, ?_, ?_,
      ⟨hK.iso (Functor.map_isZero _ HomologicalComplex.isZero_zero)⟩⟩
  · have : Subsingleton ((HomologicalComplex.zero : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
      (ModuleCat.isZero_iff_subsingleton).1 (hz i)
    exact Module.Flat.of_free
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ => hz i
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i _ => hz i

end StacksDraft.TorAmplitude

namespace AlgebraicGeometry

open StacksDraft.TorAmplitude StrictlyPerfect

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The stalk ring of the structure sheaf of `X` is commutative, at every point. -/
local instance commRing_stalk_structure_derivedTensor (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u} X.toRingedSpace).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- Restriction of scalars along any ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_dt
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along any ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_dt
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along any ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_dt
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

/-- The stalks of the terms of a bounded complex vanish outside the range of the complex. -/
private theorem isZero_modulesStalkFunctor_obj_of_notMem_Icc {X : Scheme.{u}}
    (G : CochainComplex X.Modules ℤ) (x : X) (a b : ℤ) [G.IsStrictlyGE a] [G.IsStrictlyLE b]
    (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (G.X i)) := by
  rcases not_and_or.1 hi with hi | hi
  · exact (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map_isZero
      (G.isZero_of_isStrictlyGE a i (not_le.1 hi))
  · exact (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map_isZero
      (G.isZero_of_isStrictlyLE b i (not_le.1 hi))

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj M).Additive]
  [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ)]

/-- **The derived stalk of a derived tensor product, read over the base, at one point.** If the
derived stalk of `E` at `x` has Tor amplitude in `[a, b]` over the stalk ring of `X` and that of
`F`, read over `𝒪_{S, f x}`, has Tor amplitude in `[c, d]`, then the derived stalk of
`E ⊗^L F`, read over `𝒪_{S, f x}`, has Tor amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitudeCanonical_derivedStalk_derivedTensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    (E F : DerivedCategory X.Modules) (x : X) (a b c d : ℤ)
    (hE : HasTorAmplitudeCanonical
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafOfRings.{u} X.toRingedSpace).obj x))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E) a b)
    (hF : HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
            (f.stalkMap x).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj F)) c d) :
    HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
      ((ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
            (f.stalkMap x).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj
            ((T.tensor.obj E).obj F))) (a + c) (b + d) :=
  BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars.{u}
        ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
          (f.stalkMap x).hom)).mapDerivedCategory.mapIso
      (Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoOfDerivedTensorProduct
        X.toRingedSpace.sheaf x T E F).symm) _ _
    (hasTorAmplitudeCanonical_restrictScalars_derivedTensor _ _ _ a b c d hE hF)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.toRingedSpace.sheaf).obj M).Additive]
  [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ)] in
/-- **Tor amplitude over the base at one point.** If the terms of a complex `G` of
`𝒪_X`-modules are flat over `S` at `x` and their stalks at `x` vanish outside `[a, b]`, then the
stalk complex of `G` at `x`, read over `𝒪_{S, f x}`, has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitudeCanonical_relativeStalkComplex_of_isFlatOverAt
    (G : CochainComplex X.Modules ℤ) (x : X) (a b : ℤ)
    (hz : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (G.X i)))
    (hG : ∀ i : ℤ, IsFlatOverAt f.toLRSHom.toShHom (G.X i) x) :
    HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
      (DerivedCategory.Q.obj (relativeStalkComplex f G x)) a b := by
  refine (hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ a b).2
    ⟨relativeStalkComplex f G x, fun i => hG i, ?_, ?_, ⟨Iso.refl _⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
      (ModuleCat.restrictScalars (f.stalkMap x).hom).map_isZero (hz i fun h => hi.not_ge h.1)
  · exact (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
      (ModuleCat.restrictScalars (f.stalkMap x).hom).map_isZero (hz i fun h => hi.not_ge h.2)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.toRingedSpace.sheaf).obj M).Additive]
  [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ)] in
/-- **A bounded complex of modules flat over the base has Tor amplitude over the base in its
range.** If `G` is concentrated in `[a, b]` and its terms are flat over `S`, then `G` has Tor
amplitude in `[a, b]` over `S`. -/
theorem hasTorAmplitudeOver_of_isFlatOver (G : CochainComplex X.Modules ℤ) (a b : ℤ)
    [G.IsStrictlyGE a] [G.IsStrictlyLE b]
    (hG : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i)) :
    HasTorAmplitudeOver f (DerivedCategory.Q.obj G) a b := by
  refine ⟨G, ⟨Iso.refl _⟩, fun x => (hasTorAmplitudeCanonical_iff_lift _ _ a b).1 ?_⟩
  refine hasTorAmplitudeCanonical_relativeStalkComplex_of_isFlatOverAt f G x a b
    (isZero_modulesStalkFunctor_obj_of_notMem_Icc G x a b) (fun i => hG i x)

/-- **Tor dimension over the base of a derived tensor product with a flat complex.** Let `E` be a
perfect object of `D(𝒪_X)` and `𝒢` a complex of `𝒪_X`-modules concentrated in `[c, d]`, each term
flat over `S`, with all supports inside a compact subset `Z` of `X`. Then `E ⊗^L 𝒢` has finite
Tor dimension over `S`. -/
theorem exists_hasTorAmplitudeOver_derivedTensor
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (c d : ℤ) (hc : G.IsStrictlyGE c) (hd : G.IsStrictlyLE d)
    (hG : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (Z : Set X) (hZ : IsCompact Z) (hsupp : ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ Z) :
    ∃ a b : ℤ, HasTorAmplitudeOver f ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) a b := by
  have := hc
  have := hd
  obtain ⟨I, U, hU, hfin⟩ :=
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect
      (X := X.toRingedSpace) E hE
  choose α β hαβ using hfin
  have hstalk : ∀ (i : I) (y : X), y ∈ U i → HasTorAmplitudeCanonical
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafOfRings.{u} X.toRingedSpace).obj y))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} X.toRingedSpace) y).mapDerivedCategory.obj E) (α i) (β i) :=
    fun i => (Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk
      X.toRingedSpace (U i) E (α i) (β i)).1 (hαβ i)
  have hmem : ∀ y : X, ∃ i, y ∈ U i := fun y => Opens.mem_iSup.1 (by rw [hU]; exact trivial)
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun i => ((U i : Opens X.carrier) : Set X))
    (fun i => (U i).isOpen) fun y _ => Set.mem_iUnion.2 (hmem y)
  obtain ⟨a₀, ha₀⟩ := (t.image α).bddBelow
  obtain ⟨b₀, hb₀⟩ := (t.image β).bddAbove
  refine ⟨a₀ + c, b₀ + d, (hasTorAmplitudeOver_iff_forall_derivedStalk f _ _ _).2 fun x => ?_⟩
  have hGx : ∀ c' d' : ℤ, (∀ i : ℤ, i ∉ Set.Icc c' d' →
      IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (G.X i))) →
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        ((ModuleCat.restrictScalars.{u}
            ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
              (f.stalkMap x).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj
              (DerivedCategory.Q.obj G))) c' d' := fun c' d' hz =>
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (relativeStalkComplexDerivedStalkIso f G _ (Iso.refl _) x) c' d'
      (hasTorAmplitudeCanonical_relativeStalkComplex_of_isFlatOverAt f G x c' d' hz
        fun i => hG i x)
  by_cases hxZ : x ∈ Z
  · obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht hxZ)
    refine hasTorAmplitudeCanonical_derivedStalk_derivedTensor f T E _ x a₀ b₀ c d
      (Scheme.Hom.hasTorAmplitudeCanonical_mono (ha₀ (Finset.mem_image_of_mem α hit))
        (hb₀ (Finset.mem_image_of_mem β hit)) (hstalk i x hxi))
      (hGx c d (isZero_modulesStalkFunctor_obj_of_notMem_Icc G x c d))
  · obtain ⟨i, hxi⟩ := hmem x
    have h := hasTorAmplitudeCanonical_derivedStalk_derivedTensor f T E _ x (α i) (β i)
      (a₀ + c - α i) (b₀ + d - β i) (hstalk i x hxi) (hGx _ _ fun j _ => by
        rw [ModuleCat.isZero_iff_subsingleton]
        refine not_nontrivial_iff_subsingleton.1 fun hn => hxZ (hsupp j ?_)
        exact (SheafOfModules.mem_supp_iff_nontrivial_stalk (G.X j) x).2 hn)
    rwa [add_sub_cancel, add_sub_cancel] at h

end AlgebraicGeometry


end
