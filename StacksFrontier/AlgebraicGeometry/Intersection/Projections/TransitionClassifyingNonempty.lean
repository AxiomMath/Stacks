module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingMorphism

/-!
# The classifying morphism of Tag 0B1S is defined somewhere, and on an irreducible scheme

`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifyingOpen` is the locus on which the
classifying morphism of Tag 0B1S exists: the locus where the bilinear parametrisation `G` is
nonzero. It is *not* all of the source, so before anything is said about `Φ` there has to be a
point to say it at, and before the dimension count there has to be irreducibility. Both come from
one construction: a `k`-point of the source carrying a pair of closed points of `X` and `Y` and
the parameters `c = 1`, `u = u' = u₀` with `f(u₀) = 1`, `w = 0`, `h = 0`, at which

`G(z) = f'(z) · u₀`

is nonzero as soon as `f'` is.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosedPoint`: the `k`-point of `X ×_k Y` at a
  pair of closed points of the two reduced closed subschemes.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_mem_transitionClassifyingOpen`: **the locus
  is nonempty** when `X` and `Y` are, together with the parameters and the two functionals that
  witness it — which is the data every statement about `Φ` at a point takes.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_transitionClassifyingOpen`: the same as a
  `Nonempty` instance argument.
* `…ProjectiveSpaceOfModule.irreducibleSpace_transitionClassifyingOpen_of_isIrreducible`:
  **the locus is irreducible** when `X` and `Y` are — the hypothesis the dimension count of the
  correspondence takes, and the reason nothing is lost by phrasing the construction on the locus
  rather than on the source.

## Implementation notes

**Why `w = 0` and `h = 0` and not a generic choice.** The parametrisation is
`G(z) = (c · f u) · f'(z) · u' + f'(w) · (f(u) · h(z) − f(h z) · u)`, so killing the second term
by `w = 0` leaves the first, which is a nonzero multiple of `z ↦ f'(z) · u₀` precisely when
`f(u₀) ≠ 0`. Normalising `f(u₀) = 1` makes that multiple `1`. Nothing about the pair of points is
used beyond their being closed points of `X` and of `Y`; in particular `X ∩ Y ≠ ∅` is not needed
here.

**The pair of points is produced in the `linearFunctionalPoint` form from the start.**
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_linearFunctionalPoint_mem_of_isClosed` gives a
closed point of a nonempty closed subset already cut out by a functional, which is the form in
which the nonvanishing criterion
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingOpen_transitionSections_point_iff`
reads the two projections; so no closed point has to be recognised as such afterwards. Lifting it
to the reduced closed subscheme is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_closedSubschemeOf`, and the `k`-point
of the subscheme is `AlgebraicGeometry.pointOfClosedPoint`, the two closed subschemes being
locally of finite type over the ground field.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
  [FiniteDimensional k V] [Nontrivial V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)

/-! ### The `k`-point of the base at a pair of closed points -/

/-- **The `k`-point of `X ×_k Y` at a pair of closed points** of the two reduced closed
subschemes: the morphism the universal property of the fibre product builds from the two
`k`-points, which agree over `Spec k` because each splits the structure morphism. -/
public def prodOfClosedPoint (x₁ : closedSubschemeOf k V X hXc)
    (hx₁ : IsClosed ({x₁} : Set (closedSubschemeOf k V X hXc)))
    (y₁ : closedSubschemeOf k V Y hYc)
    (hy₁ : IsClosed ({y₁} : Set (closedSubschemeOf k V Y hYc))) :
    Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc :=
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V X hXc
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hYc
  pullback.lift (pointOfClosedPoint (closedSubschemeOfToSpec k V X hXc) x₁ hx₁)
    (pointOfClosedPoint (closedSubschemeOfToSpec k V Y hYc) y₁ hy₁)
    (by rw [pointOfClosedPoint_comp, pointOfClosedPoint_comp])

/-- The `k`-point of the base splits the structure morphism through the first factor, which is the
hypothesis `hpt` of the nonvanishing criterion at a `k`-point. -/
public theorem prodOfClosedPoint_comp_toSpec (x₁ : closedSubschemeOf k V X hXc)
    (hx₁ : IsClosed ({x₁} : Set (closedSubschemeOf k V X hXc)))
    (y₁ : closedSubschemeOf k V Y hYc)
    (hy₁ : IsClosed ({y₁} : Set (closedSubschemeOf k V Y hYc))) :
    prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
        pullback.fst (closedSubschemeOfToSpec k V X hXc) (closedSubschemeOfToSpec k V Y hYc) ≫
      closedSubschemeOfToSpec k V X hXc = 𝟙 _ := by
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V X hXc
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hYc
  have hfst : prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
      pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) =
      pointOfClosedPoint (closedSubschemeOfToSpec k V X hXc) x₁ hx₁ :=
    pullback.lift_fst _ _ _
  calc prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
        pullback.fst (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfToSpec k V X hXc
      = (prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
          pullback.fst (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc)) ≫
          closedSubschemeOfToSpec k V X hXc := (Category.assoc _ _ _).symm
    _ = pointOfClosedPoint (closedSubschemeOfToSpec k V X hXc) x₁ hx₁ ≫
          closedSubschemeOfToSpec k V X hXc := by rw [hfst]
    _ = 𝟙 _ := pointOfClosedPoint_comp _ _ _

/-- The first projection of the `k`-point of the base is the chosen closed point of `X`, read in
`𝐏(V)`. -/
public theorem prodOfClosedPoint_base_fst (x₁ : closedSubschemeOf k V X hXc)
    (hx₁ : IsClosed ({x₁} : Set (closedSubschemeOf k V X hXc)))
    (y₁ : closedSubschemeOf k V Y hYc)
    (hy₁ : IsClosed ({y₁} : Set (closedSubschemeOf k V Y hYc)))
    (a : Spec (CommRingCat.of k)) :
    (prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
        pullback.fst (closedSubschemeOfToSpec k V X hXc) (closedSubschemeOfToSpec k V Y hYc) ≫
      closedSubschemeOfι k V X hXc).base a = (closedSubschemeOfι k V X hXc).base x₁ := by
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V X hXc
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hYc
  have hfst : prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
      pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) =
      pointOfClosedPoint (closedSubschemeOfToSpec k V X hXc) x₁ hx₁ :=
    pullback.lift_fst _ _ _
  have hsplit : (prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
        pullback.fst (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfι k V X hXc).base a =
      (closedSubschemeOfι k V X hXc).base
        ((prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
          pullback.fst (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc)).base a) := rfl
  rw [hsplit, hfst]
  exact congrArg (closedSubschemeOfι k V X hXc).base
    (pointOfClosedPoint_apply (closedSubschemeOfToSpec k V X hXc) x₁ hx₁ a)

/-- The second projection of the `k`-point of the base is the chosen closed point of `Y`, read in
`𝐏(V)`. -/
public theorem prodOfClosedPoint_base_snd (x₁ : closedSubschemeOf k V X hXc)
    (hx₁ : IsClosed ({x₁} : Set (closedSubschemeOf k V X hXc)))
    (y₁ : closedSubschemeOf k V Y hYc)
    (hy₁ : IsClosed ({y₁} : Set (closedSubschemeOf k V Y hYc)))
    (a : Spec (CommRingCat.of k)) :
    (prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
        pullback.snd (closedSubschemeOfToSpec k V X hXc) (closedSubschemeOfToSpec k V Y hYc) ≫
      closedSubschemeOfι k V Y hYc).base a = (closedSubschemeOfι k V Y hYc).base y₁ := by
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V X hXc
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hYc
  have hsnd : prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
      pullback.snd (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) =
      pointOfClosedPoint (closedSubschemeOfToSpec k V Y hYc) y₁ hy₁ :=
    pullback.lift_snd _ _ _
  have hsplit : (prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
        pullback.snd (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc) ≫
          closedSubschemeOfι k V Y hYc).base a =
      (closedSubschemeOfι k V Y hYc).base
        ((prodOfClosedPoint k V X Y hXc hYc x₁ hx₁ y₁ hy₁ ≫
          pullback.snd (closedSubschemeOfToSpec k V X hXc)
            (closedSubschemeOfToSpec k V Y hYc)).base a) := rfl
  rw [hsplit, hsnd]
  exact congrArg (closedSubschemeOfι k V Y hYc).base
    (pointOfClosedPoint_apply (closedSubschemeOfToSpec k V Y hYc) y₁ hy₁ a)

/-! ### A choice of parameters at which the parametrisation is nonzero -/

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] in
/-- **A normalised vector makes the parametrisation nonzero at `c = 1`, `w = 0`, `h = 0`.** The
second term of `G` is killed by `w = 0`, and the first is `z ↦ (f u₀) · f'(z) · u₀`, which at a
`z` with `f'(z) ≠ 0` is a nonzero multiple of the nonzero `u₀`. -/
public theorem transitionEnd_ne_zero_of_apply_eq_one {f f' : Module.Dual k V} (hf' : f' ≠ 0)
    {u₀ : V} (hu₀ : f u₀ = 1) :
    transitionEnd k V f f' 1 u₀ u₀ 0 0 ≠ 0 := by
  obtain ⟨z, hz⟩ : ∃ z, f' z ≠ 0 := by
    by_contra hcon
    exact hf' (LinearMap.ext fun z => not_not.mp (not_exists.mp hcon z))
  have hu₀ne : u₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu₀
    exact one_ne_zero hu₀.symm
  intro h0
  have hval : transitionEnd k V f f' 1 u₀ u₀ 0 0 z = f' z • u₀ := by
    rw [transitionEnd_apply, hu₀, mul_one, one_smul, map_zero, zero_smul, add_zero]
  rw [h0, LinearMap.zero_apply] at hval
  exact (smul_ne_zero hz hu₀ne) hval.symm

/-! ### The locus is nonempty, and irreducible -/

variable (b : Module.Basis (Fin (Module.finrank k V)) k V)

/-- **The locus on which the classifying morphism is defined is nonempty**, with the witness in
the form every statement about `Φ` at a point takes: a `k`-point of the base at a pair of closed
points of `X` and `Y`, the two functionals cutting those points out, and parameters at which the
parametrisation is nonzero. -/
public theorem exists_mem_transitionClassifyingOpen (hXn : X.Nonempty) (hYn : Y.Nonempty) :
    ∃ (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
      (_ : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
      (u₀ : V) (a : Spec (CommRingCat.of k)) (f : Module.Dual k V) (hf : f ≠ 0)
      (_ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
        linearFunctionalPoint k V f hf)
      (f' : Module.Dual k V) (hf' : f' ≠ 0)
      (_ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
        (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
        linearFunctionalPoint k V f' hf'),
      transitionEnd k V f f' 1 u₀ u₀ 0 0 ≠ 0 ∧
        (transitionSourcePoint k V X Y hXc hYc b pt 1 u₀ u₀ 0 0).base a ∈
          transitionClassifyingOpen k V X Y hXc hYc b := by
  obtain ⟨f, hf, hfX⟩ := exists_linearFunctionalPoint_mem_of_isClosed k V hXn hXc
  obtain ⟨f', hf', hfY⟩ := exists_linearFunctionalPoint_mem_of_isClosed k V hYn hYc
  obtain ⟨x₁, hx₁, hx₁c⟩ := exists_isClosed_closedSubschemeOf k V X hXc
    (linearFunctionalPoint_isClosed k V f hf) hfX
  obtain ⟨y₁, hy₁, hy₁c⟩ := exists_isClosed_closedSubschemeOf k V Y hYc
    (linearFunctionalPoint_isClosed k V f' hf') hfY
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, f u₀ = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hcon
      exact hf (LinearMap.ext fun v => not_not.mp (not_exists.mp hcon v))
    exact ⟨(f v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
  set pt := prodOfClosedPoint k V X Y hXc hYc x₁ hx₁c y₁ hy₁c with hptdef
  have hpt := prodOfClosedPoint_comp_toSpec k V X Y hXc hYc x₁ hx₁c y₁ hy₁c
  have e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf :=
    (prodOfClosedPoint_base_fst k V X Y hXc hYc x₁ hx₁c y₁ hy₁c a).trans hx₁
  have e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf' :=
    (prodOfClosedPoint_base_snd k V X Y hXc hYc x₁ hx₁c y₁ hy₁c a).trans hy₁
  have hG := transitionEnd_ne_zero_of_apply_eq_one k V hf' hu₀
  exact ⟨pt, hpt, u₀, a, f, hf, e₁, f', hf', e₂, hG,
    mem_transitionClassifyingOpen_of_transitionEnd_ne_zero pt hpt 1 u₀ u₀ 0 0 a f hf e₁ f' hf'
      e₂ hG⟩

/-- **The locus is nonempty** when `X` and `Y` are. -/
public theorem nonempty_transitionClassifyingOpen (hXn : X.Nonempty) (hYn : Y.Nonempty) :
    Nonempty (transitionClassifyingOpen k V X Y hXc hYc b).toScheme := by
  obtain ⟨pt, hpt, u₀, a, f, hf, e₁, f', hf', e₂, -, hmem⟩ :=
    exists_mem_transitionClassifyingOpen k V X Y hXc hYc b hXn hYn
  exact ⟨⟨_, hmem⟩⟩

/-- **The locus is irreducible** when `X` and `Y` are. It is a nonempty open subspace of the
irreducible source, so it is irreducible and has the same generic point: nothing is lost by
phrasing the construction of `Φ` on it rather than on the source. -/
public theorem irreducibleSpace_transitionClassifyingOpen_of_isIrreducible
    (hXirr : IsIrreducible X) (hYirr : IsIrreducible Y) :
    IrreducibleSpace (transitionClassifyingOpen k V X Y hXc hYc b).toScheme :=
  have := nonempty_transitionClassifyingOpen k V X Y hXc hYc b hXirr.nonempty hYirr.nonempty
  irreducibleSpace_transitionClassifyingOpen k V X Y hXc hYc b hXirr hYirr

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
