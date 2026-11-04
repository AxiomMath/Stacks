module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Scheme
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Smoothness read on the naive cotangent complex

**A morphism of schemes `f : X ⟶ S` is smooth if and only if it is locally of finite
presentation, the degree `-1` cohomology sheaf `H⁻¹(NL_{X/S})` of its naive cotangent complex
vanishes, and its sheaf of relative differentials `Ω_{X/S} = H⁰(NL_{X/S})` is finite locally
free.** This is [Stacks, Tag 0D0N].

## Main results

* `Stacks.Smooth.formallySmooth_stalkMap_of_isZero_homology_negOne_of_isFiniteLocallyFree`: the
  stalk maps of a morphism whose `H⁻¹(NL)` vanishes and whose `Ω` is finite locally free are
  formally smooth ring maps.
* `Stacks.Smooth.smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree`: `f` is smooth if and
  only if it is locally of finite presentation, `H⁻¹(NL_{X/S}) = 0`, and `Ω_{X/S}` is finite
  locally free.
* `Stacks.Smooth.smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree_homology_zero`: the
  same equivalence with the third clause read on `H⁰(NL_{X/S})` itself.

## References

* [Stacks Project, Tag 0D0N](https://stacks.math.columbia.edu/tag/0D0N), Lemma 37.13.7.
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L), the same criterion for
  formal smoothness.
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6), smooth is locally of
  finite presentation plus formally smooth.
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1), the differentials of a
  smooth morphism.
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J), formal smoothness of a
  ring map read on `Ω` and `H¹`.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalks of the naive
  cotangent complex.
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX), finite locally free is
  finite projective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.RelativeDifferentialStalk (algebraStalk relativeDifferentialsStalkLinearEquiv)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)

universe u

namespace Stacks.Smooth

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **A ring map whose differentials are projective and whose canonical presentation has
injective cotangent complex is formally smooth.** If `Ω[A⁄R]` is a projective `A`-module and
the map `I/I² ⟶ Ω` of the canonical presentation of `A` over `R` is injective, then `A` is
formally smooth over `R`. -/
theorem formallySmooth_of_projective_of_injective_cotangentComplex {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] (hproj : Module.Projective A (KaehlerDifferential R A))
    (hinj : Function.Injective (Algebra.Generators.self R A).toExtension.cotangentComplex) :
    Algebra.FormallySmooth R A := by
  have : Algebra.FormallySmooth R (Algebra.Generators.self R A).toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial A R))
  exact (Algebra.formallySmooth_iff R A).mpr
    ⟨hproj, (Algebra.Extension.cotangentComplex_injective_iff _).mp hinj⟩

/-- **The stalk of the differential of `NL_{X/S}` is injective when `H⁻¹(NL_{X/S})` vanishes.**
-/
theorem injective_stalkFunctor_map_d_of_isZero_homology_negOne
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1))) (x : X) :
    Function.Injective ((stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf) x).map
      ((Scheme.naiveCotangentComplex f).d (-1) 0)) := by
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf) x
  have hex : (Scheme.naiveCotangentComplex f).ExactAt (-1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hneg
  rw [AlgebraicGeometry.SheafOfModules.exactAt_iff_forall_stalk_exactAt] at hex
  have hx := (HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)).mp (hex x)
  have hz : ((stalkFunctor _ x).map ((Scheme.naiveCotangentComplex f).d (-2) (-1))) = 0 :=
    ((stalkFunctor _ x).map_isZero
      (Scheme.naiveCotangentComplex_isZero_X f (-2) (by decide) (by decide))).eq_zero_of_src _
  exact (ModuleCat.mono_iff_injective _).mp ((ShortComplex.exact_iff_mono _ hz).mp hx)

/-- **The cotangent complex of the canonical presentation of a stalk is injective when
`H⁻¹(NL_{X/S})` vanishes.** For a point `x` of `X`, the `𝒪_{X,x}`-linear map `I/I² ⟶ Ω` of the
canonical presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x` is injective. -/
theorem injective_cotangentComplex_stalk_of_isZero_homology_negOne
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1))) (x : X) :
    letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
    Function.Injective
      (Algebra.Generators.self
        (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
        (ToType (TopCat.Presheaf.stalk X.toRingedSpace.sheaf.obj
          x))).toExtension.cotangentComplex := by
  let A := inverseImageSheaf f.toLRSHom.toShHom
  let B := X.toRingedSpace.sheaf
  let a := inverseImageStructureMap f.toLRSHom.toShHom
  let := algebraStalk a.hom x
  intro ω₁ ω₂ hω
  obtain ⟨ν₁, rfl⟩ :=
    (Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne A B a x).surjective ω₁
  obtain ⟨ν₂, rfl⟩ :=
    (Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne A B a x).surjective ω₂
  refine congrArg _ (injective_stalkFunctor_map_d_of_isZero_homology_negOne f hneg x
    ((Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero A B a x).injective ?_))
  exact (Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d A B a x ν₁).trans
    (hω.trans (Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d A B a x ν₂).symm)

/-- **The Kähler differentials of a stalk are projective when `Ω_{X/S}` is finite locally
free.** For a point `x` of `X`, `Ω[𝒪_{X,x}⁄(f^{-1}𝒪_S)_x]` is a projective `𝒪_{X,x}`-module.
-/
theorem projective_kaehlerDifferential_stalk_of_isFiniteLocallyFree
    (hfree : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f)) (x : X) :
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    letI := algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x
    Module.Projective (ToType (X.sheaf.presheaf.stalk x))
      (KaehlerDifferential
        (ToType (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.stalk x))
        (ToType (X.sheaf.presheaf.stalk x))) := by
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  let := algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x
  have : Module.Free (ToType (X.sheaf.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf x)) :=
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree
      (Scheme.Hom.relativeDifferentials f) x).1
  have := Module.Free.of_equiv (relativeDifferentialsStalkLinearEquiv f x)
  exact Module.Projective.of_free

/-- **The stalk of the structural map is formally smooth.** For a point `x` of `X`, the ring map
`(f^{-1}𝒪_S)_x ⟶ 𝒪_{X,x}` is formally smooth as soon as `H⁻¹(NL_{X/S})` vanishes and `Ω_{X/S}`
is finite locally free. -/
theorem formallySmooth_stalk_inverseImageStructureMap_of_isZero_homology_negOne
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1)))
    (hfree : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f)) (x : X) :
    (CommRingCat.Hom.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (AlgebraicGeometry.inverseImageStructureMap f).hom)).FormallySmooth :=
  @formallySmooth_of_projective_of_injective_cotangentComplex _ _ _ _
    (algebraStalk (AlgebraicGeometry.inverseImageStructureMap f).hom x)
    (projective_kaehlerDifferential_stalk_of_isFiniteLocallyFree f hfree x)
    (injective_cotangentComplex_stalk_of_isZero_homology_negOne f hneg x)

/-- **The stalk maps of `f` are formally smooth.** If `H⁻¹(NL_{X/S})` vanishes and `Ω_{X/S}` is
finite locally free, then for every point `x` of `X` the stalk map `𝒪_{S,f x} ⟶ 𝒪_{X,x}` of `f`
is formally smooth. -/
theorem formallySmooth_stalkMap_of_isZero_homology_negOne_of_isFiniteLocallyFree
    (hneg : IsZero ((Scheme.naiveCotangentComplex f).homology (-1)))
    (hfree : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f)) (x : X) :
    (CommRingCat.Hom.hom (f.stalkMap x)).FormallySmooth := by
  rw [Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp f x]
  exact RingHom.FormallySmooth.comp
    (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv))
    (formallySmooth_stalk_inverseImageStructureMap_of_isZero_homology_negOne f hneg hfree x)

/-- **Smoothness read on the naive cotangent complex.** A morphism of schemes `f : X ⟶ S` is
smooth if and only if it is locally of finite presentation, `H⁻¹(NL_{X/S}) = 0`, and
`Ω_{X/S} = H⁰(NL_{X/S})` is finite locally free. -/
@[stacks 0D0N]
theorem smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree :
    AlgebraicGeometry.Smooth f ↔
      (AlgebraicGeometry.LocallyOfFinitePresentation f ∧
        IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ∧
        SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
          (Scheme.Hom.relativeDifferentials f)) := by
  constructor
  · exact fun _ => ⟨inferInstance,
      isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth f
        (formallySmoothScheme_of_smooth f),
      Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f⟩
  · rintro ⟨_, hneg, hfree⟩
    exact f.smoothLocus_eq_top_iff.mp (top_le_iff.mp fun x _ =>
      Scheme.Hom.mem_smoothLocus.mpr
        (formallySmooth_stalkMap_of_isZero_homology_negOne_of_isFiniteLocallyFree f hneg
          hfree x))

/-- **Smoothness read on the naive cotangent complex, with the third clause on `H⁰(NL_{X/S})`.**
A morphism of schemes `f : X ⟶ S` is smooth if and only if it is locally of finite presentation,
`H⁻¹(NL_{X/S}) = 0`, and `H⁰(NL_{X/S})` is finite locally free. -/
@[stacks 0D0N "the third clause read on H^0(NL_{X/S}) rather than on Omega_{X/S}"]
theorem smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree_homology_zero :
    AlgebraicGeometry.Smooth f ↔
      (AlgebraicGeometry.LocallyOfFinitePresentation f ∧
        IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ∧
        SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
          ((Scheme.naiveCotangentComplex f).homology 0)) := by
  rw [smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree f]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun _ => SheafOfModules.IsFiniteLocallyFree.of_iso
      (Scheme.naiveCotangentComplexHomologyZeroIso f).symm,
    fun _ => SheafOfModules.IsFiniteLocallyFree.of_iso
      (Scheme.naiveCotangentComplexHomologyZeroIso f)⟩

end Stacks.Smooth

end
