module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentSmoothCriterion
public import StacksFrontier.Cotangent.H1CotangentRingEquiv
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness of a morphism of schemes read on `H¹` of its stalk maps

A morphism of schemes `f : X ⟶ S` is smooth if and only if it is locally of finite presentation,
`H¹(L_{𝒪_{X,x}/𝒪_{S,f x}}) = 0` for the stalk map at every point `x` of `X`, and `Ω_{X/S}` is
finite locally free. This is the pointwise form of [Stacks, Tag 0D0N], in which the vanishing of
the sheaf `H⁻¹(NL_{X/S})` is replaced by the vanishing of the `H¹` of its stalks; it is the form
in which the spaces version, [Stacks, Tag 0D12], is reduced to schemes, the stalks of the small
étale site of an algebraic space being related to the local rings of its scheme charts.

A smooth morphism has formally smooth stalk maps, and formal smoothness includes `H¹ = 0`
([Stacks, Tag 031J]). Conversely the stalk of `Ω_{X/S}` is projective when `Ω_{X/S}` is finite
locally free, `H¹` is carried from the stalk map `𝒪_{S,f x} ⟶ 𝒪_{X,x}` to the stalk
`(f⁻¹𝒪_S)_x ⟶ 𝒪_{X,x}` of the structural map along the isomorphism of base rings
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`, and the stalk map is then formally
smooth, as in the proof of [Stacks, Tag 0D0N].

## Main results

* `Stacks.Smooth.subsingleton_h1Cotangent_stalkMap_of_smooth`: the stalk maps of a smooth
  morphism have vanishing `H¹`.
* `Stacks.Smooth.smooth_of_subsingleton_h1Cotangent_stalkMap`: the converse, under local finite
  presentation and finite local freeness of `Ω_{X/S}`.
* `Stacks.Smooth.smooth_iff_subsingleton_h1Cotangent_stalkMap`: the equivalence.

## References

* [Stacks Project, Tag 0D0N](https://stacks.math.columbia.edu/tag/0D0N)
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.RelativeDifferentialStalk (algebraStalk)

universe u

namespace Stacks.Smooth

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The stalk maps of a smooth morphism have vanishing `H¹`.** For a smooth morphism of
schemes `f : X ⟶ S` and a point `x` of `X`, `H¹` of the naive cotangent complex of the stalk map
`𝒪_{S,f x} ⟶ 𝒪_{X,x}` vanishes: the stalk map is formally smooth, and formal smoothness includes
the vanishing of `H¹`. -/
theorem subsingleton_h1Cotangent_stalkMap_of_smooth [Smooth f] (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  have hx : x ∈ f.smoothLocus := by
    rw [f.smoothLocus_eq_top_iff.mpr inferInstance]
    trivial
  exact (Scheme.Hom.mem_smoothLocus.mp hx).subsingleton_h1Cotangent

/-- The stalk `(f⁻¹𝒪_S)_x ⟶ 𝒪_{X,x}` of the structural map and the stalk map
`𝒪_{S,f x} ⟶ 𝒪_{X,x}` of `f` have the same `H¹`: they differ by the isomorphism of base rings
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`. -/
theorem subsingleton_h1Cotangent_stalk_inverseImageStructureMap_iff (x : X) :
    letI := algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x
    letI := (f.stalkMap x).hom.toAlgebra
    Subsingleton (Algebra.H1Cotangent
        (ToType (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.stalk x))
        (ToType (X.sheaf.presheaf.stalk x))) ↔
      Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  let := algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x
  let := (f.stalkMap x).hom.toAlgebra
  refine Algebra.subsingleton_h1Cotangent_iff_of_ringEquiv
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).commRingCatIsoToRingEquiv
    (RingEquiv.refl _) fun r ↦ ?_
  show ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (AlgebraicGeometry.inverseImageStructureMap f).hom) r =
    f.stalkMap x ((Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom r)
  rw [Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp f x]
  exact (congrArg (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (AlgebraicGeometry.inverseImageStructureMap f).hom))
    (Iso.hom_inv_id_apply (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x) r)).symm

/-- **A morphism locally of finite presentation whose stalk maps have vanishing `H¹` and whose
`Ω_{X/S}` is finite locally free is smooth.** At a point `x` the stalk of `Ω_{X/S}` is
projective, `H¹` of the stalk of the structural map vanishes by
`Stacks.Smooth.subsingleton_h1Cotangent_stalk_inverseImageStructureMap_iff`, so that stalk is
formally smooth ([Stacks, Tag 031J]), and so is the stalk map of `f`, which differs from it by an
isomorphism of base rings. -/
theorem smooth_of_subsingleton_h1Cotangent_stalkMap [LocallyOfFinitePresentation f]
    (hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f))
    (h : ∀ x : X, letI := (f.stalkMap x).hom.toAlgebra
      Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f x)) (X.presheaf.stalk x))) :
    Smooth f := by
  refine f.smoothLocus_eq_top_iff.mp (top_le_iff.mp fun x _ ↦ Scheme.Hom.mem_smoothLocus.mpr ?_)
  rw [Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp f x]
  refine RingHom.FormallySmooth.comp
    (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv)) ?_
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  let := algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x
  exact @Algebra.FormallySmooth.mk _ _ _ _
    (algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x)
    (projective_kaehlerDifferential_stalk_of_isFiniteLocallyFree f hfree x)
    ((subsingleton_h1Cotangent_stalk_inverseImageStructureMap_iff f x).2 (h x))

/-- **[Stacks, Tag 0D0N], read on the stalk maps.** A morphism of schemes `f : X ⟶ S` is smooth
if and only if it is locally of finite presentation, `H¹` of the naive cotangent complex of every
stalk map `𝒪_{S,f x} ⟶ 𝒪_{X,x}` vanishes, and `Ω_{X/S}` is finite locally free. -/
@[ega "IV 17.15.5" "a ⇒ c"]
theorem smooth_iff_subsingleton_h1Cotangent_stalkMap :
    Smooth f ↔
      (LocallyOfFinitePresentation f ∧
        (∀ x : X, letI := (f.stalkMap x).hom.toAlgebra
          Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f x)) (X.presheaf.stalk x))) ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
          (Scheme.Hom.relativeDifferentials f)) := by
  refine ⟨fun hf ↦ ⟨inferInstance, subsingleton_h1Cotangent_stalkMap_of_smooth f,
    ((smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree f).1 hf).2.2⟩, ?_⟩
  rintro ⟨hlfp, hH1, hfree⟩
  exact smooth_of_subsingleton_h1Cotangent_stalkMap f hfree hH1

end Stacks.Smooth

end
