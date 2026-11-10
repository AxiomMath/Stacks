module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Transporting integral closed subspaces and prime divisors along an isomorphism

Let `e : X ≅ Y` be an isomorphism of decent algebraic spaces over `S`. Taking the image along `e`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward`) is a bijection from the integral
closed subspaces of `X` onto those of `Y`, which preserves the codimension of the point set in the
ambient space and the δ-dimension of Stacks 0EDX. It restricts to a bijection from the prime
divisors of `X` onto those of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.equivOfIso`: the bijection
  `IntegralClosedSubspace X ≃ IntegralClosedSubspace Y` along an isomorphism `X ≅ Y`.
* `AlgebraicGeometry.Space.PrimeDivisor.pushforwardOfIso` and
  `AlgebraicGeometry.Space.PrimeDivisor.equivOfIso`: the image of a prime divisor along an
  isomorphism, and the resulting bijection `PrimeDivisor X ≃ PrimeDivisor Y`.

## Main results

* `AlgebraicGeometry.Space.codimension_closureSingleton_pointsMap_of_iso`: the codimension of a
  point is an isomorphism invariant.
* `AlgebraicGeometry.Space.codimension_integralClosedSubspaceSupport_pushforward_of_iso`: taking
  the image along an isomorphism does not change the codimension of the point set of an integral
  closed subspace.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.surjective_pushforward_of_iso`: every integral
  closed subspace of `Y` is the image of one of `X`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_equivOfIso`: the bijection
  preserves the δ-dimension of Stacks 0EDX.

## References

* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Codimension

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of the closure of a point under an isomorphism of spaces is the closure of the
image of that point. -/
theorem map_closureSingleton_pointsMap_of_iso (e : X ≅ Y) (x : points B S hS X) :
    IrreducibleCloseds.map (pointsMap B S hS X e.hom) (continuous_pointsMap B S hS e.hom)
        (IrreducibleCloseds.closureSingleton x) =
      IrreducibleCloseds.closureSingleton (pointsMap B S hS X e.hom x) := by
  refine IrreducibleCloseds.ext ?_
  change closure (pointsMap B S hS X e.hom '' closure {x}) =
    closure {pointsMap B S hS X e.hom x}
  rw [closure_image_closure (continuous_pointsMap B S hS e.hom), Set.image_singleton]

/-- The image of an irreducible closed subset under the map on points of an isomorphism has the
same codimension. -/
private theorem codimension_map_pointsMap_of_iso (e : X ≅ Y)
    (T : IrreducibleCloseds (points B S hS X)) :
    codimension (IrreducibleCloseds.map (pointsMap B S hS X e.hom)
        (continuous_pointsMap B S hS e.hom) T) = codimension T := by
  rw [codimension_eq_coheight, codimension_eq_coheight]
  exact (pointsHomeomorphOfIso B S hS e).isOpenEmbedding.coheight_map _

/-- **The codimension of a point is an isomorphism invariant.** The closure of the image of a
point under the map on points of an isomorphism of algebraic spaces over `S` has the codimension
of the closure of the point. -/
theorem codimension_closureSingleton_pointsMap_of_iso (e : X ≅ Y) (x : points B S hS X) :
    codimension (IrreducibleCloseds.closureSingleton (pointsMap B S hS X e.hom x)) =
      codimension (IrreducibleCloseds.closureSingleton x) := by
  rw [← map_closureSingleton_pointsMap_of_iso B S hS e x]
  exact codimension_map_pointsMap_of_iso B S hS e _

end Codimension

/-! ### Integral closed subspaces -/

section IntegralClosedSubspace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The point set of the image of an integral closed subspace along an isomorphism is the image
of its point set, as an irreducible closed subset. -/
theorem integralClosedSubspaceSupport_pushforward_of_iso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : IntegralClosedSubspace B S hS X) :
    integralClosedSubspaceSupport B S hS hY
        (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
          (isClosedImmersion_of_isIso B S hS e.hom) Z) =
      IrreducibleCloseds.map (pointsMap B S hS X e.hom) (continuous_pointsMap B S hS e.hom)
        (integralClosedSubspaceSupport B S hS hX Z) := by
  have hclosed : IsClosed (pointsMap B S hS X e.hom '' subspacePointSet B S hS X Z.subspace) :=
    (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hY
        (isClosedImmersion_of_isIso B S hS e.hom)).isClosedMap _
      (isClosed_range_pointsMap_integralClosedSubspace B S hS hX Z)
  refine IrreducibleCloseds.ext ?_
  change subspacePointSet B S hS Y
      (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom) Z).subspace =
    closure (pointsMap B S hS X e.hom '' subspacePointSet B S hS X Z.subspace)
  rw [IntegralClosedSubspace.subspacePointSet_pushforward, hclosed.closure_eq]

/-- **Taking the image along an isomorphism does not change the codimension.** The point set of
the image of an integral closed subspace of `X` in `Y` has the codimension in `|Y|` that its own
point set has in `|X|`. -/
theorem codimension_integralClosedSubspaceSupport_pushforward_of_iso
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : IntegralClosedSubspace B S hS X) :
    codimension (integralClosedSubspaceSupport B S hS hY
        (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
          (isClosedImmersion_of_isIso B S hS e.hom) Z)) =
      codimension (integralClosedSubspaceSupport B S hS hX Z) := by
  rw [integralClosedSubspaceSupport_pushforward_of_iso B S hS hX hY hYdec e Z]
  exact codimension_map_pointsMap_of_iso B S hS e _

/-- **Every integral closed subspace of `Y` is the image of one of `X`** along an isomorphism
`e : X ≅ Y` of decent algebraic spaces over `S`. -/
theorem IntegralClosedSubspace.surjective_pushforward_of_iso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) :
    Function.Surjective (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
      (isClosedImmersion_of_isIso B S hS e.hom)) := by
  intro W
  refine IntegralClosedSubspace.exists_pushforward_eq B S hS hY hX hYdec hXdec
    (isClosedImmersion_of_isIso B S hS e.hom) W ?_
  rw [(pointsMap_surjective_of_isIso B S hS e.hom).range_eq]
  exact Set.subset_univ _

/-- **The integral closed subspaces of isomorphic algebraic spaces correspond.** Taking the image
along an isomorphism `e : X ≅ Y` of decent algebraic spaces over `S` is a bijection from the
integral closed subspaces of `X` onto those of `Y`. -/
def IntegralClosedSubspace.equivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) :
    IntegralClosedSubspace B S hS X ≃ IntegralClosedSubspace B S hS Y :=
  Equiv.ofBijective
    (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
      (isClosedImmersion_of_isIso B S hS e.hom))
    ⟨IntegralClosedSubspace.injective_pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom),
      IntegralClosedSubspace.surjective_pushforward_of_iso B S hS hX hY hXdec hYdec e⟩

/-- The correspondence of integral closed subspaces along an isomorphism *is* taking the image
along it. -/
@[simp]
theorem IntegralClosedSubspace.equivOfIso_apply (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : IntegralClosedSubspace B S hS X) :
    IntegralClosedSubspace.equivOfIso B S hS hX hY hXdec hYdec e Z =
      IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom) Z :=
  rfl

/-- The codimension of the point set of an integral closed subspace is unchanged by the
correspondence along an isomorphism. -/
@[simp]
theorem codimension_integralClosedSubspaceSupport_equivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : IntegralClosedSubspace B S hS X) :
    codimension (integralClosedSubspaceSupport B S hS hY
        (IntegralClosedSubspace.equivOfIso B S hS hX hY hXdec hYdec e Z)) =
      codimension (integralClosedSubspaceSupport B S hS hX Z) :=
  codimension_integralClosedSubspaceSupport_pushforward_of_iso B S hS hX hY hYdec e Z

end IntegralClosedSubspace

/-! ### Prime divisors -/

section PrimeDivisor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of a prime divisor along an isomorphism.** For an isomorphism `e : X ≅ Y` of
algebraic spaces over `S` with `Y` decent, the prime divisor of `Y` whose underlying integral
closed subspace is the image of that of a prime divisor of `X`. -/
def PrimeDivisor.pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X) : PrimeDivisor B S hS Y :=
  (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
      (isClosedImmersion_of_isIso B S hS e.hom)
      (Z.toIntegralClosedSubspace B S hS)).toPrimeDivisor B S hS hY (by
    rw [codimension_integralClosedSubspaceSupport_pushforward_of_iso B S hS hX hY hYdec e]
    exact Z.codimension_integralClosedSubspaceSupport B S hS hX)

/-- The subfunctor underlying the image of a prime divisor along an isomorphism is the one
underlying the image of its integral closed subspace. -/
@[simp]
theorem PrimeDivisor.subspace_pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).subspace =
      (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom)
        (Z.toIntegralClosedSubspace B S hS)).subspace :=
  rfl

/-- The integral closed subspace underlying the image of a prime divisor along an isomorphism is
the image of the integral closed subspace underlying it. -/
@[simp]
theorem PrimeDivisor.toIntegralClosedSubspace_pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).toIntegralClosedSubspace B S hS =
      IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom) (Z.toIntegralClosedSubspace B S hS) :=
  IntegralClosedSubspace.ext rfl

/-- Taking the image of a prime divisor along an isomorphism is injective. -/
theorem PrimeDivisor.injective_pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) :
    Function.Injective (PrimeDivisor.pushforwardOfIso B S hS hX hY hYdec e (X := X)) := by
  intro Z W h
  refine PrimeDivisor.injective_toIntegralClosedSubspace B S hS
    (IntegralClosedSubspace.injective_pushforward B S hS hY hX hYdec
      (isClosedImmersion_of_isIso B S hS e.hom) ?_)
  rw [← PrimeDivisor.toIntegralClosedSubspace_pushforwardOfIso B S hS hX hY hYdec e Z,
    ← PrimeDivisor.toIntegralClosedSubspace_pushforwardOfIso B S hS hX hY hYdec e W, h]

/-- Taking the image of a prime divisor along an isomorphism of decent algebraic spaces is
surjective. -/
theorem PrimeDivisor.surjective_pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) :
    Function.Surjective (PrimeDivisor.pushforwardOfIso B S hS hX hY hYdec e (X := X)) := by
  intro W
  obtain ⟨Z, hZ⟩ := IntegralClosedSubspace.surjective_pushforward_of_iso B S hS hX hY hXdec
    hYdec e (W.toIntegralClosedSubspace B S hS)
  have hcod : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1 := by
    rw [← codimension_integralClosedSubspaceSupport_pushforward_of_iso B S hS hX hY hYdec e Z, hZ]
    exact W.codimension_integralClosedSubspaceSupport B S hS hY
  refine ⟨Z.toPrimeDivisor B S hS hX hcod, PrimeDivisor.eq_of_subspace_eq B S hS ?_⟩
  rw [PrimeDivisor.subspace_pushforwardOfIso,
    IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor, hZ,
    PrimeDivisor.subspace_toIntegralClosedSubspace]

/-- **The prime divisors of isomorphic algebraic spaces correspond.** For an isomorphism
`e : X ≅ Y` of decent algebraic spaces over `S`, taking the image along `e` is a bijection from
the prime divisors of `X` onto those of `Y`. -/
def PrimeDivisor.equivOfIso (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) :
    PrimeDivisor B S hS X ≃ PrimeDivisor B S hS Y :=
  Equiv.ofBijective (PrimeDivisor.pushforwardOfIso B S hS hX hY hYdec e)
    ⟨PrimeDivisor.injective_pushforwardOfIso B S hS hX hY hYdec e,
      PrimeDivisor.surjective_pushforwardOfIso B S hS hX hY hXdec hYdec e⟩

/-- The correspondence of prime divisors along an isomorphism *is* taking the image along it. -/
@[simp]
theorem PrimeDivisor.equivOfIso_apply (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : PrimeDivisor B S hS X) :
    PrimeDivisor.equivOfIso B S hS hX hY hXdec hYdec e Z =
      Z.pushforwardOfIso B S hS hX hY hYdec e :=
  rfl

/-- The point set of the image of a prime divisor along an isomorphism is the image of its point
set. -/
theorem PrimeDivisor.support_pushforwardOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)
    (Z : PrimeDivisor B S hS X) :
    (Z.pushforwardOfIso B S hS hX hY hYdec e).support B S hS Y =
      pointsMap B S hS X e.hom '' Z.support B S hS X := by
  change subspacePointSet B S hS Y
      (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom)
        (Z.toIntegralClosedSubspace B S hS)).subspace = _
  rw [IntegralClosedSubspace.subspacePointSet_pushforward]
  rfl

/-- **The two correspondences agree.** The prime divisor attached to the image of an integral
closed subspace of codimension one is the image of the prime divisor attached to it. -/
theorem IntegralClosedSubspace.toPrimeDivisor_equivOfIso (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y) (Z : IntegralClosedSubspace B S hS X)
    (h : codimension (integralClosedSubspaceSupport B S hS hX Z) = 1)
    (h' : codimension (integralClosedSubspaceSupport B S hS hY
      (IntegralClosedSubspace.equivOfIso B S hS hX hY hXdec hYdec e Z)) = 1) :
    (IntegralClosedSubspace.equivOfIso B S hS hX hY hXdec hYdec e Z).toPrimeDivisor B S hS hY
        h' =
      (Z.toPrimeDivisor B S hS hX h).pushforwardOfIso B S hS hX hY hYdec e := by
  refine PrimeDivisor.eq_of_subspace_eq B S hS ?_
  rw [IntegralClosedSubspace.subspace_toPrimeDivisor, PrimeDivisor.subspace_pushforwardOfIso,
    IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor]
  rfl

end PrimeDivisor

/-! ### The δ-dimension -/

section DeltaDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The correspondence of integral closed subspaces along an isomorphism over the base
preserves the δ-dimension of Stacks 0EDX**, the structure morphism of the source being the
composite of the isomorphism with that of the target. -/
theorem IntegralClosedSubspace.deltaDimension_equivOfIso (sY : Y ⟶ D.space)
    (hsY : IsLocallyOfFiniteType D.site D.base D.base_mem sY)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y) (e : X ≅ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D sY
        (IntegralClosedSubspace.equivOfIso D.site D.base D.base_mem hX hY hXdec hYdec e Z) =
      deltaDimension D (e.hom ≫ sY) Z :=
  IntegralClosedSubspace.deltaDimension_pushforward D sY hsY hY hX hYdec
    (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) Z

end DeltaDimension

end AlgebraicGeometry.Space

end
