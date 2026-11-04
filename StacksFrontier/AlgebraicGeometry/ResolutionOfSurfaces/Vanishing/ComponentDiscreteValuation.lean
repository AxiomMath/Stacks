module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpecializationChainInFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.GeneralDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsionExponent
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs

/-!
# Discrete valuations at the generic points of the special fibre

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` and a modification `f : X ⟶ S = Spec(A)` with the irreducible components
`C_1, …, C_r` of the special fibre enumerated — let `ξ_i` be the generic point of `C_i`, read as
a point of `X`. This file computes

`dim 𝒪_{X, ξ_i} = 1`, equivalently `coheight ξ_i = 1`,

from the standing observation following Situation 0AX8 that every component of the special fibre
has dimension one, and deduces that for `X` normal the local ring `𝒪_{X, ξ_i}` is a discrete
valuation ring. This is the fact the proof of [Stacks, Tag 0AXA] uses to read off the
multiplicities `e_i` and `d_i` of a function along the components.

It also records the tensor-power identification of the ideal sheaves of the multiples of an
effective Cartier divisor,

`ℐ_D^{⊗ n} ≅ ℐ_{nD}`,

which [Stacks, Tag 02OP] deliberately declines to build — `Stacks.Divisors.invertibleSheafSumIso`
is stated for the duals `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` — and which the same proof needs in
order to replace `Z` by `e_i Z`.

## Main definitions

The elided prefix in the first group is `AlgebraicGeometry.VanishingSituation`.

* `componentFiberGenericPoint`: the generic point of the `i`-th component of the special fibre,
  as a point of the special fibre.
* `componentGenericPoint`: the same point read in `X`.

## Main results

* `componentFiberGenericPoint_spec`, `apply_componentGenericPoint`: the defining property of the
  generic point, and the fact that it lies over the closed point of the base.
* `residueFieldTranscendenceDegree_componentGenericPoint`: `trdeg_κ κ(ξ_i) = 1`. This is where
  the dimension-one hypothesis on the components enters: by the chain lemma
  [Stacks, Tag 053V] the transcendence degree of the residue-field extension at a point equals
  the dimension of the closure of that point *inside the fibre*, and for `ξ_i` that closure is
  `C_i`.
* `ringKrullDim_stalk_componentGenericPoint_eq_one`,
  `coheight_componentGenericPoint_eq_one`: `dim 𝒪_{X, ξ_i} = 1`. The upper bound is the
  dimension formula [Stacks, Tag 0BAE] for `f`, whose correction term vanishes because `f` is
  birational and `X` integral, together with `dim 𝒪_{S, s} = 2`; the lower bound is that `ξ_i`
  is not the generic point of `X`, because it lies over the closed point of the base while the
  generic point lies over the generic point.
* `isDiscreteValuationRing_stalk_componentGenericPoint`: for `X` normal the local ring at `ξ_i`
  is a discrete valuation ring. This is Tag 00PD read off the coheight, which is
  `Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk`; the only thing
  that was missing was its hypothesis `coheight ξ_i = 1`.
* `Stacks.Divisors.negativeTwistTensorPowerIso`: `ℐ_D^{⊗ n} ≅ ℐ_{nD}` for an effective Cartier
  divisor `D`, and `Stacks.Divisors.modulePullbackNegativeTwistTensorPowerIso`, its pullback
  along an arbitrary morphism of schemes.

## Implementation notes

The hypothesis `hdim` is the observation following Situation 54.7.1, and it is an assumption here
because `VanishingSituation` as a structure does not exclude a zero-dimensional special fibre —
Situation 0AX8 does not exclude it either. It is not an assumption everywhere: its two halves are
proved in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/ComponentDimension.lean`, which
imports this file, the upper bound from the Situation alone and the lower bound from a connected
special fibre of positive dimension, and that is the form in which [Stacks, Tag 0AX9] is stated
in this library. Only the import direction keeps this file from using them.

The elementary facts about a birational morphism used below — that it carries the generic point
to the generic point, that the residue-field transcendence degree vanishes there, and hence that
the correction term of [Stacks, Tag 0BAE] vanishes everywhere — are
`StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint`.

The identification of the fibre `X_{f ξ_i}`, over which [Stacks, Tag 053V] is stated, with the
special fibre `X_s`, over which `hdim` is stated, is a transport along the equality
`f ξ_i = s` of points of the base; it is carried out once, in `fiberCongrHomeo`, and used only
through `topologicalKrullDim_closure_asFiber_componentGenericPoint`.

The tensor-power identification is proved in the Picard group rather than by building the
isomorphism: equality of Picard classes *is* isomorphism of invertible modules
(`Stacks.SheafOfModules.picardClass_eq_iff`), the class of a tensor power is a multiple
(`Stacks.Picard.classOf_tensorPower`, Tag 01CU through Tag 01CX) and the class of `ℐ_D` is the
negative of the class of `𝒪_X(D)` (`Stacks.Divisors.negativeTwistPicardClass_eq_neg`), which is
additive in `D` (`Stacks.Divisors.picardClass_pow`). No attribute is attached: the ideal-sheaf
clause is not what Tag 02OP states.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AX9](https://stacks.math.columbia.edu/tag/0AX9)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 053V](https://stacks.math.columbia.edu/tag/053V)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
* [Stacks Project, Tag 02OP](https://stacks.math.columbia.edu/tag/02OP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Transport of a fibre along an equality of base points -/

/-- The fibres over two equal points of the target are homeomorphic. -/
private def fiberCongrHomeo {X S : Scheme.{u}} (f : X ⟶ S) {y y' : S} (h : y = y') :
    f.fiber y ≃ₜ f.fiber y' := by
  cases h
  exact Homeomorph.refl _

private theorem fiberι_fiberCongrHomeo {X S : Scheme.{u}} (f : X ⟶ S) {y y' : S} (h : y = y')
    (z : f.fiber y) : f.fiberι y' (fiberCongrHomeo f h z) = f.fiberι y z := by
  cases h
  rfl

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-! ### The generic point of a component of the special fibre -/

/-- The generic point of the `i`-th irreducible component of the special fibre, as a point of
that fibre. -/
def componentFiberGenericPoint (i : Fin V.numberOfComponents) : V.specialFiber :=
  (V.component_mem_irreducibleComponents i).1.genericPoint

/-- The closure of the generic point of the `i`-th component of the special fibre is that
component. -/
theorem componentFiberGenericPoint_spec (i : Fin V.numberOfComponents) :
    IsGenericPoint (componentFiberGenericPoint V i) (V.component i) :=
  (V.component_mem_irreducibleComponents i).1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents i))

/-- The generic point of the `i`-th irreducible component of the special fibre, as a point of
the source of the modification. -/
def componentGenericPoint (i : Fin V.numberOfComponents) : V.X :=
  V.f.fiberι V.closedPoint (componentFiberGenericPoint V i)

/-- The generic point of a component of the special fibre lies over the closed point of the
base. -/
theorem apply_componentGenericPoint (i : Fin V.numberOfComponents) :
    V.f (componentGenericPoint V i) = V.closedPoint :=
  Set.mem_singleton_iff.mp
    (Set.mem_preimage.mp (V.f.fiberHomeo V.closedPoint (componentFiberGenericPoint V i)).2)

/-- The source of the modification is locally Noetherian: it is of finite type over the spectrum
of a Noetherian ring. -/
instance isLocallyNoetherian_source : IsLocallyNoetherian V.X :=
  LocallyOfFiniteType.isLocallyNoetherian V.f

/-- The local rings of the base have dimension at most two. -/
theorem ringKrullDim_stalk_base_le_two (p : V.base) :
    ringKrullDim (V.base.presheaf.stalk p) ≤ 2 := by
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
  calc (p.asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim V.A := by
        simpa only [ringKrullDim] using Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
    _ = 2 := V.dimension_two

/-- The base has dimension two, so its generic point is not its closed point. -/
theorem genericPoint_base_ne_closedPoint : genericPoint V.base ≠ V.closedPoint := by
  intro h
  have hmax : IsMax (V.closedPoint : V.base) := h ▸ isMax_genericPoint V.base
  have h0 : Order.coheight (V.closedPoint : V.base) = 0 := Order.coheight_eq_zero.2 hmax
  have hh : (IsLocalRing.maximalIdeal V.A).height = 0 := by
    rw [show IsLocalRing.maximalIdeal V.A = (V.closedPoint : V.base).asIdeal from rfl,
      idealHeight_eq_coheight, h0]
  have h2 : ((0 : ℕ∞) : WithBot ℕ∞) = 2 := by
    rw [← hh, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, V.dimension_two]
  simp at h2

/-- The generic point of a component of the special fibre is not the generic point of `X`: it
lies over the closed point of the base, while the generic point of `X` lies over the generic
point of the base. -/
theorem componentGenericPoint_ne_genericPoint (i : Fin V.numberOfComponents) :
    componentGenericPoint V i ≠ genericPoint V.X := by
  intro h
  have h1 : V.f (componentGenericPoint V i) = V.closedPoint := apply_componentGenericPoint V i
  rw [h, IsBirational.genericPoint_eq V.f V.modification.isBirational] at h1
  exact V.genericPoint_base_ne_closedPoint h1

/-- The closure of the generic point of the `i`-th component, taken inside the fibre over its
image, has the dimension of that component. The fibre over the image is transported to the
special fibre along the equality of base points. -/
theorem topologicalKrullDim_closure_asFiber_componentGenericPoint
    (i : Fin V.numberOfComponents) :
    topologicalKrullDim
        (closure ({V.f.asFiber (componentGenericPoint V i)} :
          Set (V.f.fiber (V.f (componentGenericPoint V i))))) =
      topologicalKrullDim (V.component i) := by
  have hx : V.f (componentGenericPoint V i) = V.closedPoint := apply_componentGenericPoint V i
  have hpoint : fiberCongrHomeo V.f hx (V.f.asFiber (componentGenericPoint V i)) =
      componentFiberGenericPoint V i := by
    refine (V.f.fiberι V.closedPoint).isEmbedding.injective ?_
    rw [fiberι_fiberCongrHomeo, Scheme.Hom.fiberι_asFiber]
    rfl
  have himg : (fiberCongrHomeo V.f hx) ''
      closure ({V.f.asFiber (componentGenericPoint V i)} : Set _) = V.component i := by
    rw [Homeomorph.image_closure, Set.image_singleton, hpoint]
    exact componentFiberGenericPoint_spec V i
  rw [← himg]
  exact ((fiberCongrHomeo V.f hx).image _).isHomeomorph.topologicalKrullDim_eq

/-- **The residue-field transcendence degree at the generic point of a component is one.** By
the chain lemma [Stacks, Tag 053V] it is the dimension of the closure of that point inside the
fibre, and that closure is the component, of dimension one by `hdim`. -/
theorem residueFieldTranscendenceDegree_componentGenericPoint
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (i : Fin V.numberOfComponents) :
    residueFieldTranscendenceDegree V.f (componentGenericPoint V i) = 1 := by
  let _ : Algebra (V.base.residueField (V.f (componentGenericPoint V i)))
      (V.X.residueField (componentGenericPoint V i)) :=
    (V.f.residueFieldMap (componentGenericPoint V i)).hom.toAlgebra
  have h053 := natTrdegFiber_eq_topologicalKrullDim_closure V.f (componentGenericPoint V i)
  rw [topologicalKrullDim_closure_asFiber_componentGenericPoint V i, hdim i] at h053
  have hnat : natTrdegFiber V.f (componentGenericPoint V i) = 1 := by exact_mod_cast h053
  have hbridge := natTrdegFiber_eq_toNat_trdeg_residueField V.f (componentGenericPoint V i)
  rw [hnat] at hbridge
  have hcard : Algebra.trdeg (V.base.residueField (V.f (componentGenericPoint V i)))
      (V.X.residueField (componentGenericPoint V i)) = 1 := by
    simpa using (Cardinal.toNat_eq_iff one_ne_zero).mp hbridge.symm
  change Cardinal.toENat (Algebra.trdeg (V.base.residueField (V.f (componentGenericPoint V i)))
    (V.X.residueField (componentGenericPoint V i))) = 1
  rw [hcard]
  simp

/-- **The local ring at the generic point of a component of the special fibre has dimension
one.** The upper bound is the dimension formula [Stacks, Tag 0BAE] for the modification: its
correction term vanishes because the modification is birational and `X` integral, the local ring
of the base at the closed point has dimension two, and the residue-field transcendence degree at
the point is one. The lower bound is that the point is not the generic point of `X`. -/
theorem ringKrullDim_stalk_componentGenericPoint_eq_one
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (i : Fin V.numberOfComponents) :
    ringKrullDim (V.X.presheaf.stalk (componentGenericPoint V i)) = 1 := by
  have hformula := ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le V.f
    (componentGenericPoint V i)
  rw [genericResidueFieldTranscendenceDegreeAt_eq_zero V.f
      V.modification.isBirational (componentGenericPoint V i),
    residueFieldTranscendenceDegree_componentGenericPoint V hdim i] at hformula
  have hup : ringKrullDim (V.X.presheaf.stalk (componentGenericPoint V i)) + 1 ≤ 2 := by
    refine le_trans ?_ (le_trans hformula ?_)
    · exact le_of_eq (by norm_num)
    · simpa using V.ringKrullDim_stalk_base_le_two (V.f (componentGenericPoint V i))
  have hlow : (1 : WithBot ℕ∞) ≤ ringKrullDim (V.X.presheaf.stalk (componentGenericPoint V i)) :=
    Stacks.LocalCohomology.one_le_ringKrullDim_stalk_of_ne_genericPoint _
      (componentGenericPoint_ne_genericPoint V i)
  rw [ringKrullDim_stalk_eq_coheight] at hup hlow
  have hupE : Order.coheight (componentGenericPoint V i) + 1 ≤ 1 + 1 :=
    WithBot.coe_le_coe.mp (by simpa [one_add_one_eq_two] using hup)
  have hlowE : 1 ≤ Order.coheight (componentGenericPoint V i) := by exact_mod_cast hlow
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast le_antisymm ((ENat.add_le_add_iff_right ENat.one_ne_top).mp hupE) hlowE

/-- **The coheight of the generic point of a component of the special fibre is one.** The same
statement as `ringKrullDim_stalk_componentGenericPoint_eq_one` in the form
`Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk` wants. -/
theorem coheight_componentGenericPoint_eq_one
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (i : Fin V.numberOfComponents) :
    Order.coheight (componentGenericPoint V i) = 1 := by
  have h := ringKrullDim_stalk_componentGenericPoint_eq_one V hdim i
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- **The local ring at the generic point of a component of the special fibre is a discrete
valuation ring**, for `X` normal. This is [Stacks, Tag 00PD] read off the coheight, and the
coheight is one by `coheight_componentGenericPoint_eq_one`. -/
theorem isDiscreteValuationRing_stalk_componentGenericPoint [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (i : Fin V.numberOfComponents) :
    IsDiscreteValuationRing (V.X.presheaf.stalk (componentGenericPoint V i)) :=
  Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    (coheight_componentGenericPoint_eq_one V hdim i)

end VanishingSituation

end AlgebraicGeometry

/-! ### The ideal sheaf of a multiple of an effective Cartier divisor -/

namespace Stacks.Divisors

open _root_.AlgebraicGeometry
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules.TensorPower (tensorPower isInvertible_tensorPower)

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The ideal sheaf of an effective Cartier divisor is invertible, at the spelling
`Stacks.RingedSpace.structureIsSheaf` of the sheaf condition that `Stacks.Picard` is written
over. `Stacks.Divisors.isInvertible_negativeTwist` is the same statement at the spelling
`(structureSheafRing X.toRingedSpace).property`; the two sheaf conditions are the same
proposition, and registering the re-spelling is what lets the tensor-power API of
[Stacks, Tag 01CU] resolve its hypothesis at the index the Picard group uses. -/
theorem isInvertible_negativeTwist_structureIsSheaf [IsEffectiveCartierDivisor D] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureIsSheaf X.toRingedSpace) (negativeTwist' D) :=
  isInvertible_negativeTwist D

/-- Tensoring on the right by the ideal sheaf of an effective Cartier divisor is an equivalence,
at the index the Picard group of `Stacks.Picard` is written over. This is the form in which the
tensor power of [Stacks, Tag 01CU] takes its hypothesis, and it is registered as an instance so
that `Stacks.SheafOfModules.TensorPower.tensorPower` elaborates at `ℐ_D`. -/
instance isEquivalence_tensorRightFunctor_negativeTwist [IsEffectiveCartierDivisor D] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
          (forget₂ CommRingCat RingCat) ((structureIsSheaf X.toRingedSpace))⟩).flip.obj
            ((negativeTwist' D)))).IsEquivalence :=
  have := isInvertible_negativeTwist_structureIsSheaf D
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible X.presheaf
    (structureIsSheaf X.toRingedSpace) (negativeTwist' D)

/-- **The `n`-th tensor power of the ideal sheaf of an effective Cartier divisor is the ideal
sheaf of its `n`-fold multiple**, `ℐ_D^{⊗ n} ≅ ℐ_{nD}`.

The two sides have the same Picard class: the class of a tensor power is a multiple
(`Stacks.Picard.classOf_tensorPower`), the class of `ℐ_D` is the negative of the class of
`𝒪_X(D)` (`Stacks.Divisors.negativeTwistPicardClass_eq_neg`), and the class of `𝒪_X(nD)` is `n`
times the class of `𝒪_X(D)` (`Stacks.Divisors.picardClass_pow`). Equality of Picard classes is
isomorphism of invertible modules, which is what produces the isomorphism. -/
def negativeTwistTensorPowerIso [IsEffectiveCartierDivisor D] (n : ℕ) :
    tensorPower X.presheaf (structureIsSheaf X.toRingedSpace) (negativeTwist' D) (n : ℤ) ≅
      negativeTwist' (D ^ n) := by
  haveI hN : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace)
      (negativeTwist' D) := isTensorInvertible_negativeTwist D
  refine ((Stacks.SheafOfModules.picardClass_eq_iff X.presheaf (structureIsSheaf X.toRingedSpace)
    _ _ (isInvertible_tensorPower X.presheaf (structureIsSheaf X.toRingedSpace)
      (negativeTwist' D) (n : ℤ)) (isInvertible_negativeTwist_picard (D ^ n))).1 ?_).some
  calc Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
        (tensorPower X.presheaf (structureIsSheaf X.toRingedSpace) (negativeTwist' D) (n : ℤ)) _
      = (n : ℤ) • negativeTwistPicardClass D :=
        Stacks.Picard.classOf_tensorPower X.presheaf (structureIsSheaf X.toRingedSpace)
          (negativeTwist' D) n
    _ = -picardClass (D ^ n) := by
      rw [negativeTwistPicardClass_eq_neg D, smul_neg, picardClass_pow D n]
    _ = negativeTwistPicardClass (D ^ n) := (negativeTwistPicardClass_eq_neg (D ^ n)).symm

/-- `ℐ_D^{⊗ n} ≅ ℐ_{nD}` for the other of the library's two integer tensor powers, the one over
`AlgebraicGeometry.SheafOfModules.IsInvertible` that
`AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` is stated with. The two tensor
powers are the same sheaf by
`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`. -/
def negativeTwistInvertibleTensorPowerIso [IsEffectiveCartierDivisor D] (n : ℕ) :
    Stacks.SheafOfModules.Invertible.tensorPower X.presheaf (structureIsSheaf X.toRingedSpace)
        (negativeTwist' D) (n : ℤ) ≅ negativeTwist' (D ^ n) :=
  have := isInvertible_negativeTwist_structureIsSheaf D
  eqToIso (Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower X.presheaf
      (structureIsSheaf X.toRingedSpace) (negativeTwist' D) (n : ℤ)) ≪≫
    negativeTwistTensorPowerIso D n

/-- The pullback along a morphism of schemes of the identification `ℐ_D^{⊗ n} ≅ ℐ_{nD}` of
`Stacks.Divisors.negativeTwistTensorPowerIso`. -/
def modulePullbackNegativeTwistTensorPowerIso {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsEffectiveCartierDivisor D] (n : ℕ) :
    (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj
        (tensorPower X.presheaf (structureIsSheaf X.toRingedSpace) (negativeTwist' D) (n : ℤ)) ≅
      (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj
        (negativeTwist' (D ^ n)) :=
  (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).mapIso
    (negativeTwistTensorPowerIso D n)

end Stacks.Divisors

end
