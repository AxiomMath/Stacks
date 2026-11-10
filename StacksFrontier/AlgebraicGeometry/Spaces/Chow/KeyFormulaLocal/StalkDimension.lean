module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction

/-!
# The local ring of an étale chart at a point over a codimension-two point

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n`, and let `Y ⊆ X` be an
integral closed subspace with `dim_δ(Y) = n - 2` and generic point `ζ ∈ |Y|`. The third step of
the proof of Stacks 0EQV chooses an étale neighbourhood `(U, u) → (X, ζ)` and works in the local
ring `A = 𝒪_{U, u}`, which it uses as a reduced Noetherian local ring of dimension two. This file
proves that, for **every** étale scheme chart of `X` and every point of its scheme over `ζ`.

The dimension is read off the codimension of `|Y|` in `|X|`: on any étale chart the local ring at
a point over `ζ` has Krull dimension the codimension of `|Y|` (Stacks 0ED1 and 04NA), and on the
sober irreducible space `|X|` with the dimension function `δ_{X/B}` of Stacks 0EDN, that
codimension is `δ(η) - δ(ζ) = n - (n - 2)` (Stacks 02IA), `η` the generic point of `|X|`.

## Main results

* `TopologicalSpace.codimension_closureSingleton_eq_toNat_sub`: on a sober space with a generic
  point `η` and a dimension function `d`, the codimension of the closure of a point `z` is
  `d η - d z`.
* `AlgebraicGeometry.Space.codimension_integralClosedSubspaceSupport_eq_toNat_sub`: the
  codimension of an integral closed subspace of a good integral space of δ-dimension `n` is
  `n - dim_δ`.
* `AlgebraicGeometry.Space.ringKrullDim_stalk_chartScheme_eq_two`: **the local ring of an étale
  chart at a point over the generic point of an integral closed subspace of δ-dimension `n - 2`
  has Krull dimension two.**
* `AlgebraicGeometry.Space.isReduced_stalk_chartScheme_of_isIntegralSpace` and
  `AlgebraicGeometry.Space.isNoetherianRing_stalk_chartScheme_of_isGood`: it is reduced and
  Noetherian.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

universe u

namespace TopologicalSpace

/-- **Stacks 02IA, for the closure of a point of an irreducible sober space.** On a sober space
with a generic point `η` and a dimension function `d`, the codimension of the closure of a point
`z` is `d η - d z`.

The codimension of Stacks 02I3 is a coheight in the poset of irreducible closed subsets; every
chain can be prolonged by the whole space `closure {η}`, so it is the codimension inside
`closure {η}`, which Stacks 02IA computes as `d η - d z`. -/
theorem codimension_closureSingleton_eq_toNat_sub {A : Type*} [TopologicalSpace A]
    (hA : StacksSober A) (d : DimensionFunction A) (η z : A)
    (hη : IsGenericPoint η (Set.univ : Set A)) :
    codimension (closureSingleton z) = ((d η - d z).toNat : ℕ∞) := by
  have hspec : η ⤳ z := hη.specializes (Set.mem_univ z)
  have hc := codim_closure_singleton_eq_delta_diff hA (d : A → ℤ)
    ⟨fun {_ _} hxy hne => d.strictAnti_specializes hxy hne,
      fun {_ _} himm => d.step_immediate himm⟩ η z hspec
  have htop : ∀ V : IrreducibleCloseds A, V ≤ closureSingleton η := by
    intro V
    change (V : Set A) ⊆ closure ({η} : Set A)
    rw [hη]
    exact Set.subset_univ _
  rw [← hc, codimension_eq_coheight]
  apply le_antisymm
  · refine Order.coheight_le fun p hp => ?_
    by_cases hlast : p.last = closureSingleton η
    · exact IrreducibleClosedsCodim.length_le_topCodim (closureSingleton z) (closureSingleton η) p
        hp hlast
    · let p' := p.snoc (closureSingleton η) (lt_of_le_of_ne (htop p.last) hlast)
      have hbound := IrreducibleClosedsCodim.length_le_topCodim (closureSingleton z)
        (closureSingleton η) p'
        (by simpa [p'] using hp) (by simp [p'])
      exact le_trans (by simp [p']) hbound
  · rw [IrreducibleClosedsCodim.topCodim_le_iff]
    intro p hp _
    exact Order.length_le_coheight hp.ge

end TopologicalSpace

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)

include hint in
/-- On a good integral algebraic space of δ-dimension `n`, `δ_{X/B}` takes the value `n` at the
generic point of `|X|`. -/
theorem deltaDimensionFunction_genericPoint_eq {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    haveI : QuasiSober (points D.site D.base D.base_mem X) := quasiSober_points_of_isGood D sX hX
    haveI : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
    deltaDimensionFunction D sX hX (_root_.genericPoint (points D.site D.base D.base_mem X)) =
      n := by
  have : QuasiSober (points D.site D.base D.base_mem X) := quasiSober_points_of_isGood D sX hX
  have : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
  let T : IrreducibleCloseds (points D.site D.base D.base_mem X) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have h1 : deltaDimensionClosed D sX hX Set.univ isClosed_univ =
      (deltaDimensionIrreducible D sX hX T : EInt) :=
    deltaDimensionClosed_eq_deltaDimensionIrreducible D sX hX T
  have h2 : deltaDimensionIrreducible D sX hX T =
      D.deltaValue sX (_root_.genericPoint (points D.site D.base D.base_mem X)) :=
    deltaDimensionIrreducible_eq_of_isGenericPoint D sX hX T
      (_root_.genericPoint_spec (points D.site D.base D.base_mem X))
  have h3 : ((D.deltaValue sX (_root_.genericPoint (points D.site D.base D.base_mem X)) : ℤ) :
      EInt) = (n : EInt) := by
    rwa [← h2, ← h1]
  rw [deltaDimensionFunction_apply]
  exact WithBotTop.coe_injective h3

include hint in
/-- **The codimension of an integral closed subspace is `n - dim_δ`.** On a good integral
algebraic space of δ-dimension `n`, the codimension (Stacks 02I3) of the point set of an
integral closed subspace `Y` is `n - dim_δ(Y)`. This is Stacks 02IA on the sober irreducible
space `|X|` with the dimension function `δ_{X/B}` of Stacks 0EDN. -/
theorem codimension_integralClosedSubspaceSupport_eq_toNat_sub {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Y) =
      ((n - deltaDimension D sX Y).toNat : ℕ∞) := by
  have : QuasiSober (points D.site D.base D.base_mem X) := quasiSober_points_of_isGood D sX hX
  have : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)
  have : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
  have hsupp : integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Y =
      closureSingleton (pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem)) :=
    IrreducibleCloseds.ext
      (isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 Y).symm
  rw [hsupp, codimension_closureSingleton_eq_toNat_sub
    (stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩)
    (deltaDimensionFunction D sX hX) (_root_.genericPoint (points D.site D.base D.base_mem X)) _
    (genericPoint_spec _), deltaDimensionFunction_genericPoint_eq D sX hX hint hn,
    deltaDimensionFunction_apply]
  rfl

include hint in
/-- **The local ring of an étale chart at a point over the generic point of an integral closed
subspace has dimension `n - dim_δ`.** On a good integral algebraic space of δ-dimension `n`, for
every étale scheme chart `V` of `X` and every point `u` of its scheme lying over the generic
point of an integral closed subspace `Y`, the local ring `𝒪_{V, u}` has Krull dimension
`n - dim_δ(Y)`: it is the dimension of the local ring of `X` at that point (Stacks 04NA), which
is the codimension of `|Y|` (Stacks 0ED1). -/
theorem ringKrullDim_stalk_chartScheme_eq_toNat_sub {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) (u : chartScheme V)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X V u =
      pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem)) :
    ringKrullDim ((chartScheme V).presheaf.stalk u) =
      (((n - deltaDimension D sX Y).toNat : ℕ∞) : WithBot ℕ∞) := by
  have h1 := codimension_eq_localRingDimension D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX)
    (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Y) _
    (isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 Y)
  have h2 := localRingDimension_eq_of_chartPoint D.site D.base D.base_mem hX.1
    ((SmallEtale.toOver D.site D.base D.base_mem X).obj V) V.obj.hom V.property u _
    (hu ▸ chartPoint_chartSchemeToPoints D.site D.base D.base_mem ⟨X, hX.1⟩ V u)
  rw [← h2, ← h1, codimension_integralClosedSubspaceSupport_eq_toNat_sub D sX hX hint hn Y]

include hint in
/-- **The local ring of the third step of Stacks 0EQV has dimension two.** On a good integral
algebraic space of δ-dimension `n`, the local ring of any étale scheme chart at a point over the
generic point of an integral closed subspace of δ-dimension `n - 2` has Krull dimension two. -/
theorem ringKrullDim_stalk_chartScheme_eq_two {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hY : deltaDimension D sX Y = n - 2)
    (V : SmallEtale D.site D.base D.base_mem X) (u : chartScheme V)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X V u =
      pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem)) :
    ringKrullDim ((chartScheme V).presheaf.stalk u) = 2 := by
  rw [ringKrullDim_stalk_chartScheme_eq_toNat_sub D sX hX hint hn Y V u hu, hY,
    show n - (n - 2) = 2 by ring]
  rfl

/-- The scheme of an étale chart of an integral algebraic space is reduced. -/
theorem isReduced_chartScheme_of_isIntegralSpace {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hint : IsIntegralSpace B S hS F) (V : SmallEtale B S hS F) :
    IsReduced (chartScheme V) :=
  (exists_atlas_iff_forall_etale B S hS F (fun T : Scheme.{u} => IsReduced T) hF).mp hint.1
    V.obj.left V.obj.hom V.property

include hX in
/-- The scheme of an étale chart of a good algebraic space is locally Noetherian. -/
theorem isLocallyNoetherian_chartScheme_of_isGood (V : SmallEtale D.site D.base D.base_mem X) :
    IsLocallyNoetherian (chartScheme V) :=
  (exists_atlas_iff_forall_etale D.site D.base D.base_mem X
    (fun T : Scheme.{u} => IsLocallyNoetherian T) hX.1).mp
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V.obj.left V.obj.hom V.property

/-- The local ring of an étale chart of an integral algebraic space is reduced. -/
theorem isReduced_stalk_chartScheme_of_isIntegralSpace {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hint : IsIntegralSpace B S hS F) (V : SmallEtale B S hS F) (u : chartScheme V) :
    _root_.IsReduced ((chartScheme V).presheaf.stalk u) :=
  have := isReduced_chartScheme_of_isIntegralSpace hF hint V
  inferInstance

include hX in
/-- The local ring of an étale chart of a good algebraic space is Noetherian. -/
theorem isNoetherianRing_stalk_chartScheme_of_isGood (V : SmallEtale D.site D.base D.base_mem X)
    (u : chartScheme V) : IsNoetherianRing ((chartScheme V).presheaf.stalk u) :=
  have := isLocallyNoetherian_chartScheme_of_isGood D sX hX V
  inferInstance

end AlgebraicGeometry.Space

end
