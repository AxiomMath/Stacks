module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# Étale morphisms and the naive cotangent complex

[Stacks, Tag 0G7Z] characterises étale morphisms of schemes by their naive cotangent complex: a
morphism `f : X ⟶ S` is étale if and only if it is locally of finite presentation and both
cohomology sheaves `H⁻¹(NL_{X/S})` and `H⁰(NL_{X/S})` vanish.

## Main results

* `Stacks.NaiveCotangentEtale.injective_stalkFunctor_map_naiveCotangentComplex_d_iff`: the stalk
  at `x` of the one nonzero differential of `NL_{X/S}` is injective exactly when
  `H¹(L_{𝒪_{X,x}/(f^{-1}𝒪_S)_x})` vanishes.
* `Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff`:
  `H⁻¹(NL_{X/S}) = 0` exactly when that vanishing holds at every point.
* `Stacks.NaiveCotangentEtale.formallyUnramified_iff_isZero_homology_zero`: `H⁰(NL_{X/S}) = 0`
  exactly when `f` is formally unramified.
* `AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_isZero_naiveCotangentHomology`: `f`
  is étale if and only if it is locally of finite presentation and `H⁻¹(NL_{X/S})` and
  `H⁰(NL_{X/S})` vanish.

## References

* [Stacks Project, Tag 0G7Z](https://stacks.math.columbia.edu/tag/0G7Z)
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves
  of `NL_{X/S}`
* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9), formal unramifiedness
  and the vanishing of `Ω_{X/S}`
* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI), étale morphisms
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)

universe u

namespace Stacks.NaiveCotangentEtale

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The stalk of the structural map, against the stalk map of `f`.** The stalk at `x` of the
structural map `f^{-1}𝒪_S ⟶ 𝒪_X` is the stalk map `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` of `f` precomposed
with the isomorphism `(f^{-1}𝒪_S)_x ≅ 𝒪_{S,f(x)}`. -/
theorem stalkFunctor_map_inverseImageStructureMap_eq (x : X) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageStructureMap f.toLRSHom.toShHom).hom =
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom ≫ f.stalkMap x := by
  rw [Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp f x]
  exact ((Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom_inv_id_assoc _).symm

/-- **Formal smoothness of the stalk of the structural map is formal smoothness of the stalk
map.** The ring map `(f^{-1}𝒪_S)_x ⟶ 𝒪_{X,x}` is formally smooth if and only if the stalk map
`𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` of `f` is. -/
theorem formallySmooth_stalk_inverseImageStructureMap_iff (x : X) :
    (CommRingCat.Hom.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageStructureMap f.toLRSHom.toShHom).hom)).FormallySmooth ↔
      (f.stalkMap x).hom.FormallySmooth := by
  constructor
  · intro h
    rw [Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp f x]
    exact RingHom.FormallySmooth.comp
      (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
        (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).inv)) h
  · intro h
    rw [stalkFunctor_map_inverseImageStructureMap_eq f x]
    exact RingHom.FormallySmooth.comp
      (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
        (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom)) h

/-- **The stalk of the structural map of a formally unramified morphism is formally
unramified.** For `f` formally unramified, the ring map `(f^{-1}𝒪_S)_x ⟶ 𝒪_{X,x}` is formally
unramified. -/
theorem formallyUnramified_stalk_inverseImageStructureMap [FormallyUnramified f] (x : X) :
    (CommRingCat.Hom.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (inverseImageStructureMap f.toLRSHom.toShHom).hom)).FormallyUnramified := by
  rw [stalkFunctor_map_inverseImageStructureMap_eq f x]
  exact RingHom.FormallyUnramified.comp
    (RingHom.FormallyUnramified.of_surjective (ConcreteCategory.bijective_of_isIso
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom).2)
    (AlgebraicGeometry.FormallyUnramified.stalkMap f x)

/-- Injectivity of `d` is injectivity of `c` when they are intertwined by a bijection and an
injection. -/
private theorem injective_iff_injective_of_comp_eq {α β γ δ : Type*} {d : α → β} {c : γ → δ}
    {e : α → γ} {e' : β → δ} (he : e.Bijective) (he' : e'.Injective) (h : ∀ x, e' (d x) = c (e x)) :
    d.Injective ↔ c.Injective := by
  rw [← he'.of_comp_iff, ← Function.Injective.of_comp_iff' c he]
  exact iff_of_eq (congrArg _ (funext h))

/-- **Injectivity of the cotangent complex of the stalk algebra makes the stalk of the
differential of `NL_{X/S}` injective.** If the map `cotangentComplex` of the canonical
presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x` is injective, then so is the stalk at `x` of the
one nonzero differential of `NL_{X/S}`. -/
theorem injective_stalkFunctor_map_naiveCotangentComplex_d (x : X)
    (h : letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
      Function.Injective (Algebra.Generators.self
        (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
        (ToType (TopCat.Presheaf.stalk
          X.toRingedSpace.sheaf.obj x))).toExtension.cotangentComplex) :
    Function.Injective ((stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf) x).map
      ((Scheme.naiveCotangentComplex f).d (-1) 0)) := by
  let A := inverseImageSheaf f.toLRSHom.toShHom
  let B := X.toRingedSpace.sheaf
  let a := inverseImageStructureMap f.toLRSHom.toShHom
  let := algebraStalk a.hom x
  have hleg := fun ω => Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d A B a x ω
  exact (injective_iff_injective_of_comp_eq
    (Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne A B a x).bijective
    (Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero A B a x).injective hleg).mpr h

/-- **Injectivity of the stalk of the differential of `NL_{X/S}` makes the cotangent complex of
the stalk algebra injective.** If the stalk at `x` of the one nonzero differential of `NL_{X/S}`
is injective, then so is the map `cotangentComplex` of the canonical presentation of `𝒪_{X,x}`
over `(f^{-1}𝒪_S)_x`. -/
theorem injective_cotangentComplex_stalk (x : X)
    (h : Function.Injective ((stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf) x).map
      ((Scheme.naiveCotangentComplex f).d (-1) 0))) :
    letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
    Function.Injective (Algebra.Generators.self
      (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
      (ToType (TopCat.Presheaf.stalk
        X.toRingedSpace.sheaf.obj x))).toExtension.cotangentComplex := by
  let A := inverseImageSheaf f.toLRSHom.toShHom
  let B := X.toRingedSpace.sheaf
  let a := inverseImageStructureMap f.toLRSHom.toShHom
  let := algebraStalk a.hom x
  have hleg := fun ω => Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d A B a x ω
  exact (injective_iff_injective_of_comp_eq
    (Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne A B a x).bijective
    (Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero A B a x).injective hleg).mp h

/-- **The stalk of the differential of `NL_{X/S}` is injective exactly when the cotangent
complex of the stalk algebra is.** -/
theorem injective_stalkFunctor_map_naiveCotangentComplex_d_iff (x : X) :
    letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
    (Function.Injective ((stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf) x).map
        ((Scheme.naiveCotangentComplex f).d (-1) 0)) ↔
      Function.Injective (Algebra.Generators.self
        (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
        (ToType (TopCat.Presheaf.stalk
          X.toRingedSpace.sheaf.obj x))).toExtension.cotangentComplex) :=
  ⟨injective_cotangentComplex_stalk f x, injective_stalkFunctor_map_naiveCotangentComplex_d f x⟩

/-- **`NL_{X/S}` is exact in degree `-1` exactly when the cotangent complex of every stalk
algebra is injective.** -/
theorem exactAt_negOne_naiveCotangentComplex_iff :
    (Scheme.naiveCotangentComplex f).ExactAt (-1) ↔
      ∀ x : X, letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
        Function.Injective (Algebra.Generators.self
          (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
          (ToType (TopCat.Presheaf.stalk
            X.toRingedSpace.sheaf.obj x))).toExtension.cotangentComplex := by
  have := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf)
  rw [AlgebraicGeometry.SheafOfModules.exactAt_iff_forall_stalk_exactAt]
  refine forall_congr' fun x => ?_
  rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.exact_iff_mono _ (((stalkFunctor _ x).map_isZero
      (Scheme.naiveCotangentComplex_isZero_X f (-2) (by decide) (by decide))).eq_zero_of_src _),
    ModuleCat.mono_iff_injective]
  exact injective_stalkFunctor_map_naiveCotangentComplex_d_iff f x

/-- **`H⁻¹(NL_{X/S}) = 0` exactly when the cotangent complex of every stalk algebra is
injective.** -/
theorem isZero_homology_negOne_naiveCotangentComplex_iff :
    IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ↔
      ∀ x : X, letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
        Function.Injective (Algebra.Generators.self
          (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
          (ToType (TopCat.Presheaf.stalk
            X.toRingedSpace.sheaf.obj x))).toExtension.cotangentComplex :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).symm.trans
    (exactAt_negOne_naiveCotangentComplex_iff f)

/-- **`H⁰(NL_{X/S}) = 0` is formal unramifiedness.** A morphism `f` is formally unramified if
and only if the degree-zero cohomology sheaf of `NL_{X/S}` vanishes. -/
theorem formallyUnramified_iff_isZero_homology_zero :
    FormallyUnramified f ↔ IsZero ((Scheme.naiveCotangentComplex f).homology 0) :=
  (Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials f).trans
    (Scheme.naiveCotangentComplexHomologyZeroIso f).isZero_iff.symm

/-- **The stalk criterion for formal smoothness of the stalk map.** For a formally unramified
`f`, the stalk map of `f` at `x` is formally smooth exactly when the cotangent complex of the
canonical presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x` is injective. -/
theorem formallySmooth_stalkMap_iff_injective_cotangentComplex [FormallyUnramified f] (x : X) :
    (f.stalkMap x).hom.FormallySmooth ↔
      letI := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
      Function.Injective (Algebra.Generators.self
        (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
        (ToType (TopCat.Presheaf.stalk
          X.toRingedSpace.sheaf.obj x))).toExtension.cotangentComplex := by
  let := algebraStalk (inverseImageStructureMap f.toLRSHom.toShHom).hom x
  have : Algebra.FormallyUnramified
      (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
      (ToType (TopCat.Presheaf.stalk X.toRingedSpace.sheaf.obj x)) :=
    formallyUnramified_stalk_inverseImageStructureMap f x
  constructor
  · intro h
    have hfs : Algebra.FormallySmooth
        (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
        (ToType (TopCat.Presheaf.stalk X.toRingedSpace.sheaf.obj x)) :=
      (formallySmooth_stalk_inverseImageStructureMap_iff f x).mpr h
    exact Stacks.Smooth.injective_cotangentComplex_of_formallySmooth _ _
  · intro h
    have key : Algebra.FormallySmooth
        (ToType (TopCat.Presheaf.stalk (inverseImageSheaf f.toLRSHom.toShHom).obj x))
        (ToType (TopCat.Presheaf.stalk X.toRingedSpace.sheaf.obj x)) :=
      ⟨inferInstance, (Algebra.Extension.subsingleton_h1Cotangent _).mpr h⟩
    exact (formallySmooth_stalk_inverseImageStructureMap_iff f x).mp key

end Stacks.NaiveCotangentEtale

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Étale morphisms by the naive cotangent complex.** A morphism of schemes `f : X ⟶ S` is
étale if and only if it is locally of finite presentation and both cohomology sheaves
`H⁻¹(NL_{X/S})` and `H⁰(NL_{X/S})` of its naive cotangent complex vanish. -/
@[stacks 0G7Z]
theorem etale_iff_locallyOfFinitePresentation_and_isZero_naiveCotangentHomology (f : X ⟶ S) :
    Etale f ↔
      (LocallyOfFinitePresentation f ∧
        IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ∧
        IsZero ((Scheme.naiveCotangentComplex f).homology 0)) := by
  constructor
  · intro _
    exact ⟨inferInstance,
      (Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff f).mpr fun x =>
        (Stacks.NaiveCotangentEtale.formallySmooth_stalkMap_iff_injective_cotangentComplex f x).mp
          (Scheme.Hom.mem_smoothLocus.mp (f.smoothLocus_eq_top.ge (Set.mem_univ x))),
      (Stacks.NaiveCotangentEtale.formallyUnramified_iff_isZero_homology_zero f).mp inferInstance⟩
  · rintro ⟨hlfp, hneg, hzero⟩
    have : FormallyUnramified f :=
      (Stacks.NaiveCotangentEtale.formallyUnramified_iff_isZero_homology_zero f).mpr hzero
    have : Smooth f := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
      rintro x -
      exact (Stacks.NaiveCotangentEtale.formallySmooth_stalkMap_iff_injective_cotangentComplex
        f x).mpr
        ((Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff f).mp hneg x)
    rw [Etale.iff_flat_and_formallyUnramified]
    exact ⟨inferInstance, inferInstance, hlfp⟩

end AlgebraicGeometry

end
