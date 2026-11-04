module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.SinglePointGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeMonotone

/-!
# The degree of a zero cycle as a sum of dimensions of rings of global functions

In Situation 0EDT let `p : X ⟶ Y` be a proper morphism of good algebraic spaces over the base
with `Y` playing the role of `Spec(k)`: reduced, with a single point, and with vanishing
induced dimension function. **Stacks 0ESH** computes the degree of a zero cycle
`α = ∑ n_i [Z_i]` on `X` as

    deg(α) = ∑ n_i dim_k Γ(Z_i, 𝒪_{Z_i}),

where `k = Γ(Y, 𝒪_Y)` and `Γ(Z_i, 𝒪_{Z_i})` is a `k`-algebra through the structure morphism
`Z_i ⟶ Y`.

This is `AlgebraicGeometry.Space.cycleDegree_eq_finsum` together with the identification of the
weight of Stacks 0EP0 at `Z_i` with `dim_k Γ(Z_i, 𝒪_{Z_i})`. An integral closed subspace of
δ-dimension zero has a single point, because the induced dimension function drops strictly
along a nontrivial specialization inside it and is bounded below by the vanishing dimension
function of `Y`; so `Z_i` and `Y` are both spectra of fields, Stacks 047Z, and
`AlgebraicGeometry.Space.residueDegree_eq_finrank_globalFunctions` reads the degree of the
residue field extension as the dimension of the global functions.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.subsingleton_points_of_deltaDimension_eq_zero`:
  an integral closed subspace of δ-dimension zero over a one-point base with vanishing dimension
  function has a single point.
* `AlgebraicGeometry.Space.cycleResidueDegree_eq_finrank_globalFunctions`: the degree of such a
  subspace over the base is the dimension of its ring of global functions.
* `AlgebraicGeometry.Space.cycleDegree_eq_finsum_finrank` and
  `AlgebraicGeometry.Space.cycleDegree_eq_sum_finrank`: **Stacks 0ESH**, in the two shapes in
  which `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree` presents a cycle, with
  `deg(Z_i)` read as the source reads it, `dim_k Γ(Z_i, 𝒪_{Z_i})`.

## Implementation notes

**How `Spec(k)` is modelled.** As in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree`
the target `Y` is a good algebraic space over the base with a single point and with vanishing
induced dimension function, and here it is moreover *reduced*. The three conditions together
say exactly that `Y` is the spectrum of a field — a reduced decent algebraic space with one
point is `Spec(k)` with `k = Γ(Y, 𝒪_Y)`, Stacks 047Z,
`AlgebraicGeometry.Space.exists_iso_yoneda_spec_of_subsingleton_points` — and `Spec(k)` satisfies
each of them, so none is an extra hypothesis on the source's situation. Reducedness is not implied
by the other two in this modelling (the spectrum of `k[ε]/(ε²)` has one point), and it cannot be
dropped from the statement: over a one-point base with non-reduced ring of global functions `A`
the global functions of a point `Z_i` are a field killed by the nilradical of `A`, which has
`A`-rank zero, so the right hand side would vanish while the degree does not.

**The field `k`.** It is the ring of global functions `Γ(Y, 𝒪_Y)` of the target, and
`Γ(Z_i, 𝒪_{Z_i})` is a `k`-algebra by pullback along `Z_i ⟶ X ⟶ Y`; this is the structure in
which the source's `dim_k Γ(Z_i, 𝒪_{Z_i})` is taken.

**The degree is the cycle-level degree.** As in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree`, `deg(α)` is the coefficient of the
proper pushforward `p_*α` on `Y`, which is how Stacks 0ESG defines it before passing to `CH_0`.

## References

* [Stacks Project, Tag 0ESH](https://stacks.math.columbia.edu/tag/0ESH)
* [Stacks Project, Tag 047Z](https://stacks.math.columbia.edu/tag/047Z)
* [Stacks Project, Tag 0EP0](https://stacks.math.columbia.edu/tag/0EP0)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An integral closed subspace of δ-dimension zero of a good algebraic space proper over a
one-point base with vanishing dimension function has a single point. -/
theorem IntegralClosedSubspace.subsingleton_points_of_deltaDimension_eq_zero
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZdim : deltaDimension D sX Z = 0) :
    Subsingleton (points D.site D.base D.base_mem Z.subspace.toFunctor) := by
  subst hbase
  have hnonneg : ∀ x : points D.site D.base D.base_mem X, 0 ≤ D.deltaValue (p ≫ sY) x := by
    intro x
    rw [← hδ (pointsMap D.site D.base D.base_mem X p x)]
    exact inducedDimensionValue_le_of_comp D.site D.base D.base_mem hX.1 hY.1
      D.isAlgebraicSpace D.delta.toFun p sY hX.2.2 hY.2.2 x
  have hall : ∀ w ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace,
      w = Z.ambientGenericPoint D.site D.base D.base_mem := by
    intro w hw
    by_contra hne
    have hlt : D.deltaValue (p ≫ sY) w <
        D.deltaValue (p ≫ sY) (Z.ambientGenericPoint D.site D.base D.base_mem) :=
      inducedDimensionValue_lt_of_mem_of_ne D (p ≫ sY) hX Z hw hne
    have hzero : D.deltaValue (p ≫ sY)
        (Z.ambientGenericPoint D.site D.base D.base_mem) = 0 := hZdim
    have hge := hnonneg w
    omega
  refine ⟨fun a b => (Z.isClosedEmbedding_pointsMap D.site D.base D.base_mem hX.1).injective ?_⟩
  rw [hall _ ⟨a, rfl⟩, hall _ ⟨b, rfl⟩]

/-- **The degree of an integral closed subspace of δ-dimension zero.** Over a reduced one-point
base with vanishing dimension function the degree `[R(Z) : k]` of `Z → Spec(k)` is
`dim_k Γ(Z, 𝒪_Z)`. -/
theorem cycleResidueDegree_eq_finrank_globalFunctions
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hYred : HasEtaleLocalProperty D.site D.base D.base_mem Y
      (fun T : Scheme.{u} => IsReduced T))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZdim : deltaDimension D sX Z = 0) :
    letI : Algebra (globalFunctions' D.site D.base D.base_mem Y)
        (globalFunctions' D.site D.base D.base_mem Z.subspace.toFunctor) :=
      (globalFunctionsMap D.site D.base D.base_mem
        (ObjectProperty.homMk (Z.subspace.ι ≫ p) :
          (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ :
              AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).toAlgebra
    cycleResidueDegree D sX hX sY hY p (Z.ambientGenericPoint D.site D.base D.base_mem) =
      Module.finrank (globalFunctions' D.site D.base D.base_mem Y)
        (globalFunctions' D.site D.base D.base_mem Z.subspace.toFunctor) := by
  let : Algebra (globalFunctions' D.site D.base D.base_mem Y)
      (globalFunctions' D.site D.base D.base_mem Z.subspace.toFunctor) :=
    (globalFunctionsMap D.site D.base D.base_mem
      (ObjectProperty.homMk (Z.subspace.ι ≫ p) :
        (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ :
            AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).toAlgebra
  have hZsub := IntegralClosedSubspace.subsingleton_points_of_deltaDimension_eq_zero
    D sX hX sY hY hbase hδ Z hZdim
  have hkey := residueDegree_eq_finrank_globalFunctions D.site D.base D.base_mem
    Z.subspace.toFunctor Y Z.isClosedSubspace.1 hY.1 Z.isIntegralSpace.isDecentSpace
    (D.isDecentSpace_of_isGood sY hY) hZsub hpt
    Z.isIntegralSpace.hasEtaleLocalProperty_isReduced hYred (Z.subspace.ι ≫ p)
    (Z.genericPoint D.site D.base D.base_mem)
  have _ : Mono (residueFieldMorphism D.site D.base D.base_mem Z.subspace.toFunctor
      Z.isIntegralSpace.isDecentSpace (Z.genericPoint D.site D.base D.base_mem)) :=
    (residueFieldRepresentative D.site D.base D.base_mem Z.subspace.toFunctor
      Z.isIntegralSpace.isDecentSpace (Z.genericPoint D.site D.base D.base_mem)).2.2
  have hmono : Mono (residueFieldMorphism D.site D.base D.base_mem Z.subspace.toFunctor
      Z.isIntegralSpace.isDecentSpace (Z.genericPoint D.site D.base D.base_mem) ≫
      Z.subspace.ι) := mono_comp _ _
  have hbij : Function.Bijective (residueFieldHom D.site D.base D.base_mem
      Z.subspace.toFunctor X hX.1 Z.isIntegralSpace.isDecentSpace
      (D.isDecentSpace_of_isGood sX hX) Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem)) :=
    (ConcreteCategory.isIso_iff_bijective _).1
      ((isIso_residueFieldHom_iff_mono D.site D.base D.base_mem Z.subspace.toFunctor X hX.1
        Z.isIntegralSpace.isDecentSpace (D.isDecentSpace_of_isGood sX hX) Z.subspace.ι
        (Z.genericPoint D.site D.base D.base_mem)).2 hmono)
  have hone : residueDegree D.site D.base D.base_mem Z.subspace.toFunctor X hX.1
      Z.isIntegralSpace.isDecentSpace (D.isDecentSpace_of_isGood sX hX) Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem) = 1 :=
    degreeOfFieldHom_eq_one_of_bijective hbij
  rw [← hkey, residueDegree_comp D.site D.base D.base_mem Z.subspace.toFunctor X Y hX.1 hY.1
    Z.isIntegralSpace.isDecentSpace (D.isDecentSpace_of_isGood sX hX)
    (D.isDecentSpace_of_isGood sY hY) Z.subspace.ι p (Z.genericPoint D.site D.base D.base_mem),
    hone, mul_one]
  rfl

/-- Two products with the same factor agree if the other factors agree whenever it is nonzero. -/
private theorem mul_congr_of_ne_zero {a b : ℕ} {c : ℤ} (h : c ≠ 0 → a = b) :
    c * a = c * b := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [h hc]

/-- **Stacks 0ESH, in the shape in which this library presents a cycle.** Let `p : X ⟶ Y` be a
proper morphism of good algebraic spaces over the base, with `Y` reduced, with a single point
and with vanishing induced dimension function — the situation of `Y = Spec(k)`. Writing a zero
cycle `α` on `X` as the coefficient family `Z ↦ n_Z` on the integral closed subspaces of `X`,

    deg(α) = ∑ n_Z dim_k Γ(Z, 𝒪_Z),

where `k = Γ(Y, 𝒪_Y)`. -/
@[stacks 0ESH "deg(Z) is dim_k Γ(Z, 𝒪_Z), as in the source. Spec(k) is modelled as a reduced \
good algebraic space over the base with one point and vanishing dimension function (which by \
Stacks 047Z is the spectrum of the field k = Γ(Y, 𝒪_Y)); the cycle is the coefficient family on \
the integral closed subspaces, so the sum runs over all of them"]
theorem cycleDegree_eq_finsum_finrank (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hYred : HasEtaleLocalProperty D.site D.base D.base_mem Y
      (fun T : Scheme.{u} => IsReduced T))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0) :
    cycleDegree D sX hX sY hY hbase hp W α =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 Z *
        (letI : Algebra (globalFunctions' D.site D.base D.base_mem Y)
              (globalFunctions' D.site D.base D.base_mem Z.subspace.toFunctor) :=
            (globalFunctionsMap D.site D.base D.base_mem
              (ObjectProperty.homMk (Z.subspace.ι ≫ p) :
                (⟨Z.subspace.toFunctor, Z.isClosedSubspace.1⟩ :
                    AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).toAlgebra
        (Module.finrank (globalFunctions' D.site D.base D.base_mem Y)
          (globalFunctions' D.site D.base D.base_mem Z.subspace.toFunctor) : ℤ)) := by
  rw [cycleDegree_eq_finsum D sX hX sY hY hbase hp hpt hδ W α]
  refine finsum_congr fun Z => ?_
  exact mul_congr_of_ne_zero fun hZ =>
    cycleResidueDegree_eq_finrank_globalFunctions D sX hX sY hY hbase hpt hYred hδ Z (α.2.2 Z hZ)

/-- **Stacks 0ESH, in the source's shape.** In the situation of
`AlgebraicGeometry.Space.cycleDegree_eq_finsum_finrank`, let the zero cycle `α` be presented as
a finite sum `α = ∑ n_i [Z_i]` over pairwise distinct integral closed subspaces `Z_i ⊆ X`. Then

    deg(α) = ∑ n_i dim_k Γ(Z_i, 𝒪_{Z_i}),

where `k = Γ(Y, 𝒪_Y)`. -/
@[stacks 0ESH "the same modelling of Spec(k) as in \
AlgebraicGeometry.Space.cycleDegree_eq_finsum_finrank; this is its restatement for a cycle \
given as a finite sum over pairwise distinct integral closed subspaces"]
theorem cycleDegree_eq_sum_finrank (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hYred : HasEtaleLocalProperty D.site D.base D.base_mem Y
      (fun T : Scheme.{u} => IsReduced T))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0)
    {J : Type v} [Fintype J] (Z : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : Function.Injective Z) (n : J → ℤ) (hn : ∀ i, α.1 (Z i) = n i)
    (hsupp : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X,
      (∀ i, Z i ≠ T) → α.1 T = 0) :
    cycleDegree D sX hX sY hY hbase hp W α =
      ∑ i : J, n i *
        (letI : Algebra (globalFunctions' D.site D.base D.base_mem Y)
              (globalFunctions' D.site D.base D.base_mem (Z i).subspace.toFunctor) :=
            (globalFunctionsMap D.site D.base D.base_mem
              (ObjectProperty.homMk ((Z i).subspace.ι ≫ p) :
                (⟨(Z i).subspace.toFunctor, (Z i).isClosedSubspace.1⟩ :
                    AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)).toAlgebra
        (Module.finrank (globalFunctions' D.site D.base D.base_mem Y)
          (globalFunctions' D.site D.base D.base_mem (Z i).subspace.toFunctor) : ℤ)) := by
  rw [cycleDegree_eq_sum D sX hX sY hY hbase hp hpt hδ W α Z hZ n hn hsupp]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact mul_congr_of_ne_zero fun hn0 =>
    cycleResidueDegree_eq_finrank_globalFunctions D sX hX sY hY hbase hpt hYred hδ (Z i)
      (α.2.2 (Z i) ((hn i).trans_ne hn0))

end AlgebraicGeometry.Space

end
