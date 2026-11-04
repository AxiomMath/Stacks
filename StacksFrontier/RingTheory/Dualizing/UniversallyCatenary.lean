module

public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Defs
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary

/-!
# Universal catenarity of a ring with a dualizing complex

A Noetherian ring `A` with a dualizing complex is universally catenary: every `A`-algebra of
finite type is catenary. The dualizing complex passes to such an algebra `C`, because `C` is
essentially of finite type over `A`, and the dimension function of the transported complex makes
`Spec C` catenary.

## Main results

* `Dualizing.isUniversallyCatenary_of_isDualizingComplex` — a Noetherian ring admitting a
  dualizing complex is universally catenary.

## Implementation notes

Catenarity of `Spec C` is read off the dimension function through
`TopologicalSpace.isCatenarySpace_and_topCodim_eq_of_isDimensionFunction`, which speaks of
`TopologicalSpace.IsDimensionFunctionForCatenary` rather than the bundled
`TopologicalSpace.DimensionFunction`; the two encodings order the conjuncts of an immediate
specialization differently, so the bundled function is unpacked into the unbundled predicate
here. The resulting `IrreducibleClosedsCodim.IsCatenarySpace` is then moved to `Ring.IsCatenary`
along `Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum`.

The dualizing complex is a complex of modules in the ring's own universe, which is the shape in
which `Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType` produces the transported
complex.

## References

* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
-/

@[expose] public section

open CategoryTheory IrreducibleClosedsCodim TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- A catenary space has a catenary order of irreducible closed subsets: between comparable
irreducible closeds the maximal chains have one common finite length. -/
private theorem catenaryOrder_of_catenarySpace {X : Type*} [TopologicalSpace X]
    (hX : IrreducibleClosedsCodim.IsCatenarySpace X) :
    Catenary.IsCatenaryOrder (IrreducibleCloseds X) := by
  intro Y Z hYZ
  obtain ⟨hfin, heq⟩ := hX Y Z hYZ
  refine ⟨⟨(topCodim Y Z).toNat, ?_⟩, ?_⟩
  · intro s hs ht
    have h := length_le_topCodim Y Z s hs ht
    rw [← ENat.natCast_toNat hfin] at h
    exact_mod_cast h
  · intro p q hphead hplast hqhead hqlast
    let p' : LTSeries (IrreducibleCloseds X) :=
      ⟨p.length, p.toFun, fun i => (p.step i).lt⟩
    let q' : LTSeries (IrreducibleCloseds X) :=
      ⟨q.length, q.toFun, fun i => (q.step i).lt⟩
    have hpmax : IsMaximalChain p' Y Z := ⟨hphead, hplast, p.step⟩
    have hqmax : IsMaximalChain q' Y Z := ⟨hqhead, hqlast, q.step⟩
    have hplen := heq p' hpmax
    have hqlen := heq q' hqmax
    exact_mod_cast hplen.trans hqlen.symm

/-- A ring with catenary prime spectrum is catenary. -/
private theorem ringCatenary_of_catenarySpace {R : Type*} [CommRing R]
    (hR : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R)) :
    Ring.IsCatenary R :=
  AlgebraicGeometry.ringIsCatenary_of_catenaryOrder
    ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mpr
      (catenaryOrder_of_catenarySpace hR))

/-- A dimension function on the prime spectrum makes the ring catenary. -/
private theorem ringCatenary_of_dimensionFunction {R : Type*} [CommRing R]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum R)) : Ring.IsCatenary R :=
  ringCatenary_of_catenarySpace (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction
    (PrimeSpectrum R) (stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩) δ
    ⟨δ.strictAnti_specializes, δ.step_immediate⟩).1

/-- **An algebra of finite type is essentially of finite type**, witnessed by itself: no
localization is needed. -/
public theorem isEssentiallyOfFiniteType_of_finiteType {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (hC : Algebra.FiniteType A C) :
    IsEssentiallyOfFiniteType A C (algebraMap A C) := by
  let algOld : Algebra A C := inferInstance
  let algNew : Algebra A C := (algebraMap A C).toAlgebra
  have hft : @Algebra.FiniteType A C _ _ algNew :=
    Algebra.algebra_ext algOld algNew (fun _ => rfl) ▸ hC
  let _ : Algebra A C := algNew
  exact ⟨C, inferInstance, inferInstance, hft, IsUnit.submonoid C, inferInstance,
    inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 0A80.** A Noetherian ring admitting a dualizing complex is universally
catenary: every algebra of finite type over it is catenary. -/
@[stacks 0A80 "universally catenary"]
theorem isUniversallyCatenary_of_isDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsDualizingComplex K) :
    Ring.IsUniversallyCatenary A := by
  intro C _ _ hC
  obtain ⟨hC', L, hL⟩ :=
    exists_isDualizingComplex_of_isEssentiallyOfFiniteType
      (isEssentiallyOfFiniteType_of_finiteType hC) K hK
  let _ : IsNoetherianRing C := hC'
  exact ringCatenary_of_dimensionFunction (dualizingDimensionFunction.{u, u} L hL)

end Dualizing

end
