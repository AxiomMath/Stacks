module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationNormalPuncturedSurface
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Sober.Defs

/-!
# The spectrum of a field as the base of the theory of cycles on algebraic spaces

Let `k` be a field and `B` a big fppf site containing `Spec k`. The algebraic space `Spec k` over
`Spec k` is quasi-separated, Noetherian and universally catenary, and the constant zero is a
dimension function on its one point: it is a base for Situation 0EDT. This is the situation of
Spaces over Fields and of Section 0ESF of Chow Homology of Algebraic Spaces, in which the degree
of a zero cycle and the intersection numbers live.

## Main definitions

* `AlgebraicGeometry.Space.fieldSpaceSituation`: `(Spec k, δ = 0)` as a
  `AlgebraicGeometry.Space.BaseSpaceDimensionSituation`.

## Main results

* `AlgebraicGeometry.Space.isUniversallyCatenary_yoneda_baseObject`: the algebraic space
  `Spec k` is universally catenary: a decent algebraic space locally of finite type over `k` has a
  dimension function on its points (Stacks 0ED5) and is therefore catenary (Stacks 02IA).
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- The algebraic space `Spec k` has a single point. -/
instance subsingleton_points_yoneda_baseObject :
    Subsingleton (points B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))) :=
  haveI : Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseObject k B hk)) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  (schemePointsHomeomorph B (Spec (.of k)) hk (baseObject k B hk)).toEquiv.subsingleton

/-- **The algebraic space `Spec k` is universally catenary.** A decent algebraic space locally of
finite type over `Spec k` carries a dimension function on its points (Stacks 0ED5, with
`Spec k` universally catenary as a scheme), and a sober space with a dimension function is
catenary (Stacks 02IA). -/
theorem isUniversallyCatenary_yoneda_baseObject :
    IsUniversallyCatenary B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk)) := by
  intro Y hY hYdec g hg
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (baseObject k B hk)) := inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  obtain ⟨δ, -⟩ := inducedDimensionValue_isDimensionFunction B (Spec (.of k)) hk
    (T := baseObject k B hk) (Scheme.isUniversallyCatenary_spec_of_field k)
    (Stacks.Chow.fieldDimensionFunction k) hY
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B (Spec (.of k)) hk hYdec) g hg
  have := t0Space_points_of_isDecentSpace B (Spec (.of k)) hk hY hYdec
  have := quasiSober_points_of_isDecentSpace B (Spec (.of k)) hk hY hYdec
  exact (isCatenarySpace_and_topCodim_eq_of_isDimensionFunction _
    (stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩) δ
    ⟨fun _ _ hxy hne => δ.strictAnti_specializes hxy hne,
      fun _ _ hxy => δ.step_immediate hxy⟩).1

/-- The constant zero dimension function on the one point of the algebraic space `Spec k`. -/
def fieldSpaceDimensionFunction :
    DimensionFunction (points B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))) where
  toFun := fun _ => 0
  strictAnti_specializes := fun {x y} _ hne => absurd (Subsingleton.elim x y) hne
  step_immediate := fun {x y} h => absurd (Subsingleton.elim x y) h.2.1

/-- **The spectrum of a field, with the zero dimension function, as the base of Situation 0EDT.**
It is an `abbrev`, so that its site, base and space are reducibly `B`, `Spec k` and the algebraic
space `Spec k`. -/
abbrev fieldSpaceSituation : BaseSpaceDimensionSituation.{u} where
  site := B
  base := Spec (.of k)
  base_mem := hk
  terminal_mem := B.contains_terminal
  space := yoneda.obj (baseObject k B hk)
  isAlgebraicSpace := isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)
  quasiSeparated := isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of k)) hk
    (yoneda.obj (baseObject k B hk)) B.contains_terminal
    ⟨_, inferInstanceAs (QuasiSeparatedSpace (Spec (.of k))), ⟨Functor.RepresentableBy.yoneda _⟩⟩
  locallyNoetherian := hasEtaleLocalProperty_of_representable B (Spec (.of k)) hk
    (yoneda.obj (baseObject k B hk)) (P := fun T : Scheme.{u} => IsLocallyNoetherian T)
    (baseObject k B hk) (Iso.refl _)
    (inferInstanceAs (IsLocallyNoetherian (Spec (.of k))))
  universallyCatenary := isUniversallyCatenary_yoneda_baseObject k B hk
  delta := fieldSpaceDimensionFunction k B hk

/-- An algebraic space proper over `k` is good over the base `Spec k` of Situation 0EDT: proper
morphisms are separated, hence quasi-separated, and of finite type. -/
theorem isGood_fieldSpaceSituation_of_isProper (X : AlgebraicSpaces B (Spec (.of k)) hk)
    {f : X.1 ⟶ yoneda.obj (baseObject k B hk)} (hf : IsProper B (Spec (.of k)) hk f) :
    (fieldSpaceSituation k B hk).IsGood f :=
  ⟨X.2, isQuasiSeparated_of_isSeparated B (Spec (.of k)) hk hf.1, hf.2.1.1⟩

/-- The identity of `Spec k` is proper. -/
theorem isProper_id_baseObject :
    IsProper B (Spec (.of k)) hk (𝟙 (yoneda.obj (baseObject k B hk))) :=
  isProper_of_isClosedImmersion B (Spec (.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) _
    (isClosedImmersion_of_isIso B (Spec (.of k)) hk _)

/-- The algebraic space `Spec k` is good over itself. -/
theorem isGood_fieldSpaceSituation_id :
    (fieldSpaceSituation k B hk).IsGood (𝟙 (yoneda.obj (baseObject k B hk))) :=
  isGood_fieldSpaceSituation_of_isProper k B hk
    ⟨_, isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
    (isProper_id_baseObject k B hk)

/-- The algebraic space `Spec k` is integral. -/
theorem isIntegralSpace_yoneda_baseObject :
    IsIntegralSpace B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk)) :=
  isIntegralSpace_yoneda_baseTerminal k B hk

/-- **The point of `Spec k`**: the algebraic space `Spec k` as an integral closed subspace of
itself, the unique one. -/
def fieldSpacePoint :
    IntegralClosedSubspace B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk)) :=
  IntegralClosedSubspace.top B (Spec (.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))
    (isIntegralSpace_yoneda_baseObject k B hk)

/-- The dimension function of `fieldSpaceSituation` vanishes. -/
theorem fieldSpaceSituation_delta
    (x : points B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))) :
    (fieldSpaceSituation k B hk).delta x = 0 :=
  rfl

end AlgebraicGeometry.Space

end
