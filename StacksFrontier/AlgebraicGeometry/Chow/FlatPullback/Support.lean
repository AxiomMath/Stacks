module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonvanishing of flat pullback coefficients

The coefficient of a flat pullback at a point `x` of `T` is the coefficient of the cycle at
`h x` times the multiplicity of `x` in the inverse image of the reduced closure of `h x`. This
file shows that multiplicity is nonzero whenever `x` is a generic point of that inverse image,
and so computes where the pulled-back coefficient can fail to vanish.

## Main results

* `Stacks.Chow.generic_stalk_artinian`: the stalk at the generic point of an irreducible
  component of a locally Noetherian scheme is artinian.
* `Stacks.Chow.componentMultiplicity_ne_zero`: multiplicities of components of a closed
  subscheme are nonzero.
* `Stacks.Chow.flatPullbackCoeff_ne_zero_of_genericPoint`: the flat pullback coefficient is
  nonzero at such a generic point.
* `Stacks.Chow.exists_comap_genericPoint_over`: every point over `y` specializes from the
  image of a generic point of the inverse image of the closure of `y`.

## References

* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- In a `T0` space the generic point of an irreducible component is maximal for the
specialization order. -/
theorem genericPoint_isMax {X : Type u} [TopologicalSpace X] [T0Space X]
    (x : X) (hx : closure ({x} : Set X) ∈ irreducibleComponents X) :
    @IsMax X (specializationOrder X).toLE x :=
  fun y (hxy : y ⤳ x) ↦ specializes_iff_closure_subset.mpr
    (hx.2 isIrreducible_singleton.closure hxy.closure_subset)

/-- On a locally Noetherian scheme the stalk at the generic point of an irreducible component
is artinian. -/
theorem generic_stalk_artinian {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (ξ : genericPoints Z) : IsArtinianRing (Z.presheaf.stalk ξ.1) := by
  let : PartialOrder Z := specializationOrder Z
  have : Ring.KrullDimLE 0 (Z.presheaf.stalk ξ.1) := by
    rw [Ring.krullDimLE_iff, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    exact_mod_cast (Order.coheight_eq_zero.mpr (genericPoint_isMax ξ.1 ξ.2)).le
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- The multiplicity of an irreducible component of a closed subscheme of a locally Noetherian
scheme is nonzero. -/
theorem componentMultiplicity_ne_zero {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (ξ : genericPoints Z) :
    componentMultiplicity i ξ ≠ 0 := by
  unfold componentMultiplicity
  let R := X.presheaf.stalk (i ξ.1)
  let M := Z.presheaf.stalk ξ.1
  let : Module R M := Module.compHom M (i.stalkMap ξ.1).hom
  let : Algebra R M := (i.stalkMap ξ.1).hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap R M) := i.stalkMap_surjective ξ.1
  rw [Module.length_eq_of_surjective hsurj]
  let : IsArtinianRing M := generic_stalk_artinian ξ
  exact_mod_cast (ENat.toNat_pos Module.length_pos.ne' Module.length_ne_top).ne'

/-- The reduced closed subscheme cut out by the vanishing ideal of the closure of a point is
irreducible. -/
theorem vanishingSubscheme_irreducibleSpace {Y : Scheme.{u}} (y : Y) :
    IrreducibleSpace
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).subscheme) := by
  let i := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).subschemeι
  have hirr : IsIrreducible (Set.range i) := by
    simpa [i, Scheme.IdealSheafData.range_subschemeι] using isIrreducible_singleton.closure
  exact i.isClosedEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
    (Subtype.irreducibleSpace hirr)

/-- In a quasi-sober `T0` space, the image of any point under a continuous map lies in the closure
of the image of the generic points. -/
theorem continuous_image_genericPoints_dense {X Y : Type*}
    [TopologicalSpace X] [QuasiSober X] [T0Space X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (x : X) :
    f x ∈ closure (f '' (genericPoints X : Set X)) :=
  image_closure_subset_closure_image hf (Set.mem_image_of_mem f (by simp [genericPoints.closure]))

/-- A flat pullback coefficient is nonzero at a point which is the image of a generic point of
the inverse image of the reduced closure of its image, provided the dimension condition holds
and the coefficient downstairs is nonzero. -/
theorem flatPullbackCoeff_ne_zero_of_genericPoint
    (C : ChowSituation.{u}) {T Y : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (h : T ⟶ Y) (e : ℕ) (r : ℤ)
    (β : CycleGroup C sY r) (y : Y) (x : T)
    (ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subscheme))
    (hξ : (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap h).subschemeι) ξ.1 = x)
    (hmap : h x = y)
    (hdim : relativeDimension C.dimensionFunction sT x = r + (e : ℤ))
    (hβ : β.1 y ≠ 0) :
    flatPullbackCoeff C sT sY h e r β x ≠ 0 := by
  classical
  cases hmap
  unfold flatPullbackCoeff
  apply mul_ne_zero hβ
  unfold flatPullbackWeight closedSubschemeCycleCoeff
  let H : ∃ η : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h x} : Set Y))).comap h).subscheme),
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h x} : Set Y))).comap h).subschemeι) η.1 = x ∧
        relativeDimension C.dimensionFunction sT x = r + (e : ℤ) :=
    ⟨ξ, hξ, hdim⟩
  rw [dite_eq_left H]
  have hchoose : Classical.choose H = ξ :=
    Subtype.ext <| ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h x} : Set Y))).comap h).subschemeι.isClosedEmbedding.injective
        ((Classical.choose_spec H).1.trans hξ.symm)
  rw [hchoose]
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : IsLocallyNoetherian
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h x} : Set Y))).comap h).subscheme) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h x} : Set Y))).comap h).subschemeι)
  exact componentMultiplicity_ne_zero _ ξ

/-- A point of `T` lying over `y` is a specialization of the image of a generic point of the
inverse image of the reduced closure of `y`, and that image still lies over `y`. -/
theorem exists_comap_genericPoint_over
    {T Y : Scheme.{u}} (h : T ⟶ Y) (y : Y) (x : T) (hxy : h x = y) :
    ∃ ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap h).subscheme),
      x ∈ closure ({(((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap h).subschemeι) ξ.1} : Set T) ∧
        h ((((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).comap h).subschemeι) ξ.1) = y := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({y} : Set Y))
  let J := I.comap h
  let Z := J.subscheme
  have hmem : ∀ t : T, t ∈ Set.range J.subschemeι ↔ h t ∈ closure ({y} : Set Y) := fun t ↦ by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    rfl
  obtain ⟨z, hz⟩ : x ∈ Set.range J.subschemeι := (hmem x).mpr (hxy ▸ subset_closure rfl)
  let W : irreducibleComponents Z :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  let ξ : genericPoints Z := genericPoints.ofComponent W
  have hξz : ξ.1 ⤳ z := by
    rw [specializes_iff_mem_closure, (genericPoints.isGenericPoint_ofComponent W).def]
    exact mem_irreducibleComponent
  have hmap_gen : h (J.subschemeι ξ.1) ⤳ y := by
    simpa [hz, hxy] using hξz.map (h.continuous.comp J.subschemeι.continuous)
  have hξpre := (hmem _).mp ⟨ξ.1, rfl⟩
  refine ⟨ξ, ?_, (hmap_gen.antisymm (specializes_iff_mem_closure.mpr hξpre)).eq⟩
  rw [← hz]
  exact specializes_iff_mem_closure.mp (hξz.map J.subschemeι.continuous)

/-- A morphism from an irreducible scheme whose range is the closure of a point carries the
generic point of the source to that point. -/
theorem image_genericPoint_eq_of_range_eq_closure {X Z : Scheme.{u}}
    [IrreducibleSpace Z] (i : Z ⟶ X) (x : X)
    (hi : Set.range i.base = closure ({x} : Set X)) :
    i.base (genericPoint Z) = x := by
  apply IsGenericPoint.eq _ isGenericPoint_closure
  simpa [Set.image_univ, hi] using (genericPoint_spec Z).image i.continuous

end Stacks.Chow
