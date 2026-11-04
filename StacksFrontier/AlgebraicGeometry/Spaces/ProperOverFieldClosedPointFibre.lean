module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedPointInfiniteFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.InfiniteFibreContractedPiece
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# An infinite fibre over a closed point, for a source proper over a field

Let `k` be a field, let `X` be an algebraic space over `Spec k` isomorphic to the functor of
points of an object `U` of the big fppf site which is proper over `Spec k`, let `Z` be an
algebraic space separated over `Spec k` and let `g : X ⟶ Z`. If the fibre of `g` over some
point of `|Z|` is infinite, then the fibre over some *closed* point of `|Z|` is infinite.

This is `AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre` with each of its
hypotheses discharged from properness of `U` over `Spec k` and separatedness of `Z`:

* `g` is proper, hence locally of finite type and universally closed, because `X` is proper
  over `Spec k` and `Z` is separated over it — part (2) of [Stacks, Tag 04NX];
* `X` and `Z` are decent algebraic spaces, properness of `g` and separatedness of `Z` making
  both morphisms separated, hence quasi-separated, very reasonable, reasonable and decent
  ([Stacks, Tag 03M5] and [Stacks, Tag 0ABY]);
* the point space of `X` is that of the scheme representing `U`, which is a Jacobson space
  because that scheme is locally of finite type over a field.

The hypotheses are those of the contracted-curve extraction step
`AlgebraicGeometry.Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre`, which is
keyed on a closed point of `|Z|` with an infinite fibre; this supplies that closed point from
the mere existence of an infinite fibre, which is the form in which the contraction process of
[Stacks, Tag 0AEM] meets it.

## Main results

* `AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre_of_properRepresentation`:
  the statement above.
* `AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre_of_not_forall_finite`: the
  same, from the failure of finiteness of all the fibres on points.

## References

* [Stacks Project, Tag 03M5](https://stacks.math.columbia.edu/tag/03M5)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 07W4](https://stacks.math.columbia.edu/tag/07W4)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (k : Type u) [Field k]
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- A separated morphism of algebraic spaces over `Spec k` is decent. -/
private theorem isDecent_of_isSeparated
    {X Y : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Y) {f : X ⟶ Y}
    (hf : IsSeparated B (Spec (CommRingCat.of k)) hk f) :
    IsDecent B (Spec (CommRingCat.of k)) hk f :=
  isDecent_of_isReasonable B (Spec (CommRingCat.of k)) hk hX hY f
    (isReasonable_of_isVeryReasonable B (Spec (CommRingCat.of k)) hk hX hY
      (isVeryReasonable_of_isQuasiSeparated B (Spec (CommRingCat.of k)) hk hX hY
        (isQuasiSeparated_of_isSeparated B (Spec (CommRingCat.of k)) hk hf)))

/-- **An infinite fibre over a point of `|Z|` gives an infinite fibre over a closed point of
`|Z|`, for a source proper over a field.**  Let `X` be an algebraic space over `Spec k`
isomorphic to the functor of points of an object `U` of the big fppf site proper over `Spec k`,
let `Z` be separated over `Spec k` and let `g : X ⟶ Z` have an infinite fibre over the point
`y` of `|Z|`. Then some closed point of `|Z|` has an infinite fibre.

Properness of `U` over `Spec k` and separatedness of `Z` give everything that
`AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre` asks for: `g` is proper,
both spaces are decent, and `|X| ≅ |U|` is a Jacobson space. -/
theorem exists_isClosed_singleton_infinite_fibre_of_properRepresentation
    (U : BigFppfOver B (Spec (CommRingCat.of k)) hk)
    (hproper : _root_.AlgebraicGeometry.IsProper (B.inclusion.map U.hom))
    {X Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk X) (e : X ≅ yoneda.obj U)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (g : X ⟶ Z) (y : points B (Spec (CommRingCat.of k)) hk Z)
    (hinf : {x : points B (Spec (CommRingCat.of k)) hk X |
      pointsMap B (Spec (CommRingCat.of k)) hk X g x = y}.Infinite) :
    ∃ w : points B (Spec (CommRingCat.of k)) hk Z, IsClosed {w} ∧
      {x : points B (Spec (CommRingCat.of k)) hk X |
        pointsMap B (Spec (CommRingCat.of k)) hk X g x = w}.Infinite := by
  let := hproper
  have hT : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
    isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _
  have ht : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hk)) :
      BigFppfOver B (Spec (CommRingCat.of k)) hk)) :=
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hk)))).isTerminalObj yoneda _
  -- `g` is proper: `X` is proper over `Spec k` and `Z` is separated over it
  obtain ⟨pU, hpUeq⟩ : ∃ pU : U ⟶ (Over.mk (𝟙 (B.obj hk)) :
      BigFppfOver B (Spec (CommRingCat.of k)) hk),
      (BigFppfOver.toScheme B (Spec (CommRingCat.of k)) hk).map pU = B.inclusion.map U.hom :=
    ⟨Over.homMk U.hom, rfl⟩
  have hpUproper : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B (Spec (CommRingCat.of k)) hk).map pU) := by
    rw [hpUeq]
    exact hproper
  have hpU : IsProper B (Spec (CommRingCat.of k)) hk (yoneda.map pU) :=
    isProper_yoneda_map B (Spec (CommRingCat.of k)) hk pU hpUproper
  have hbase : g ≫ z = e.hom ≫ yoneda.map pU := ht.hom_ext _ _
  have hgz : IsProper B (Spec (CommRingCat.of k)) hk (g ≫ z) := by
    rw [hbase]
    exact (isProper_isIso_comp_iff B (Spec (CommRingCat.of k)) hk e.hom (yoneda.map pU)).2 hpU
  have hgproper : IsProper B (Spec (CommRingCat.of k)) hk g :=
    isProper_of_comp_of_isSeparated B (Spec (CommRingCat.of k)) hk hX hZ hT g z hgz hsep
  -- both spaces are decent
  have hgdecent := isDecent_of_isSeparated B k hk hX hZ hgproper.1
  have hzdecent := isDecent_of_isSeparated B k hk hZ hT hsep
  have hZdec : IsDecentSpace B (Spec (CommRingCat.of k)) hk Z :=
    isDecentSpace_of_isDecent B (Spec (CommRingCat.of k)) hk hZ hT z
      (isDecentSpace_yoneda B (Spec (CommRingCat.of k)) hk _) hzdecent
  have hXdec : IsDecentSpace B (Spec (CommRingCat.of k)) hk X :=
    isDecentSpace_of_isDecent B (Spec (CommRingCat.of k)) hk hX hZ g hZdec hgdecent
  -- the point space of `X` is that of a scheme locally of finite type over `k`
  have hjac := jacobsonSpace_points_of_iso B (Spec (CommRingCat.of k)) hk e
    (jacobsonSpace_points_yoneda B (Spec (CommRingCat.of k)) hk U
      (jacobsonSpace_of_locallyOfFiniteType_over_field (B.inclusion.map U.hom)))
  exact exists_isClosed_singleton_infinite_fibre B (Spec (CommRingCat.of k)) hk hX hZ g
    hgproper.2.1.1 hgproper.2.2 hXdec hZdec hjac y hinf

/-- **If not all the fibres of `g` on points are finite, then the fibre over some closed point
of `|Z|` is infinite.**  This is
`AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre_of_properRepresentation`
with the point carrying the infinite fibre produced from the failure of finiteness. -/
theorem exists_isClosed_singleton_infinite_fibre_of_not_forall_finite
    (U : BigFppfOver B (Spec (CommRingCat.of k)) hk)
    (hproper : _root_.AlgebraicGeometry.IsProper (B.inclusion.map U.hom))
    {X Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk X) (e : X ≅ yoneda.obj U)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (g : X ⟶ Z)
    (hnot : ¬ ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
      {x : points B (Spec (CommRingCat.of k)) hk X |
        pointsMap B (Spec (CommRingCat.of k)) hk X g x = y}.Finite) :
    ∃ w : points B (Spec (CommRingCat.of k)) hk Z, IsClosed {w} ∧
      {x : points B (Spec (CommRingCat.of k)) hk X |
        pointsMap B (Spec (CommRingCat.of k)) hk X g x = w}.Infinite := by
  obtain ⟨y, hy⟩ := not_forall.1 hnot
  exact exists_isClosed_singleton_infinite_fibre_of_properRepresentation B k hk U hproper hX e hZ
    z hsep g y hy

end AlgebraicGeometry.Space

end
