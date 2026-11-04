module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusPoints
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothLocusDeformation
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothOpenSubstackRestriction
public import StacksFrontier.Deformation.Examples.Geometric.SchemesUnobstructedUnconditional

/-!
# `Curves^{lci+}` is smooth over `Spec(ℤ)` (Stacks 0DZX, part (1)), and its consequences

Let `W` be the open substack of the stack of curves where `Curves → Spec(ℤ)` is smooth. A point of
`|Curves^{lci+}|` is the class of a field-valued point mapping to the point `x₀` classifying a
proper scheme `X` of dimension at most one over a field `k`, a local complete intersection over
`k` smooth except at finitely many points (Stacks 0DZX, part (3)). The deformation category `Def_X`
is then unobstructed (Stacks 0DZQ), so `x₀` lies in `W` (Stacks 0DZU, over a Cohen ring of `k`
when `k` has characteristic `p > 0` and over `k` itself in characteristic zero). Hence
`|Curves^{lci+}| ⊆ |W|`, so `Curves^{lci+} ⊆ W` (Stacks 06FJ), and `Curves^{lci+}` is smooth over
`Spec(ℤ)`. Smoothness of `Curves^{nodal}` (Stacks 0E00) and of `𝓜̄` and `𝓜̄_g` (Stacks 0E79)
follow by restriction to open substacks.

Everything is stated on `AlgebraicGeometry.curvesAlgebraicStack B hZ h`, which takes `h`, the
algebraicity of the stack of curves (Stacks 0D5A), and uses `hlfp`, the local finite presentation
of `Curves → Spec(ℤ)` (Stacks 0DSS), through Stacks 0DZU.

## Main results

* `AlgebraicGeometry.smoothLocus_property_curvesSmallPoint_of_lci`: the point classifying a proper
  scheme over a field which is a local complete intersection smooth away from finitely many
  points lies in the smooth locus of `Curves → Spec(ℤ)`.
* `AlgebraicGeometry.isSmoothOverIntegers_lciPlus`: Stacks 0DZX, part (1).
* `AlgebraicGeometry.isSmoothOverIntegers_nodal`: Stacks 0E00.
* `AlgebraicGeometry.isSmoothOverIntegers_stable` and
  `AlgebraicGeometry.isSmoothOverIntegers_stableOfGenus`: Stacks 0E79, given the open substacks
  `𝓜̄` and `𝓜̄_g` (Stacks 0E76 and 0E78).

## References

* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0DZU](https://stacks.math.columbia.edu/tag/0DZU)
* [Stacks Project, Tag 0DZQ](https://stacks.math.columbia.edu/tag/0DZQ)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Examples

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The point of an lci curve smooth off finitely many points lies in the smooth locus.** Let `X`
be a proper scheme of dimension at most one over a field `k` which is a local complete intersection
over `k` and smooth over `k` except at finitely many points. With `h` the algebraicity of the stack
of curves (Stacks 0D5A) and `hlfp` its local finite presentation over `Spec ℤ` (Stacks 0DSS), the
point classifying `X` lies in the open substack where `Curves → Spec ℤ` is smooth. -/
theorem smoothLocus_property_curvesSmallPoint_of_lci {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
    (hdim : topologicalKrullDim X.left ≤ 1)
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    {W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)}
    (hW : Stack.IsSmoothLocus B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W)
    (hlci : IsLocalCompleteIntersectionMorphism X.hom)
    (hfin : (X.hom.smoothLocus : Set X.left)ᶜ.Finite) :
    W.property (curvesSmallPoint B hZ X hk hdim) := by
  have hsyn : IsLocalCompleteIntersectionOverField X.hom :=
    (syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism X.hom).2 ⟨inferInstance, hlci⟩
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · have : CharP k (ringChar k) := ringChar.charP k
    obtain ⟨Λ, _, _, _, -, ⟨e⟩⟩ := IsCohenRing.exists_residueField_ringEquiv (ringChar k) hp k
    let : Algebra Λ k := (e.toRingHom.comp (IsLocalRing.residue Λ)).toAlgebra
    have hsurj : Function.Surjective (algebraMap Λ k) :=
      e.surjective.comp IsLocalRing.residue_surjective
    exact (smoothLocus_property_curvesSmallPoint_iff_of_isCohenRing B hZ X hk hdim h hlfp hW
      hsurj).2 (isSmooth_baseProjection_schemeDeformationCategoryProjection_of_lci X hdim hsyn hfin)
  · have : CharP k 0 := hp ▸ ringChar.charP k
    have : CharZero k := CharP.charP_to_charZero k
    exact (smoothLocus_property_curvesSmallPoint_iff (Λ := k) B hZ X hk hdim h hlfp hW
      Function.surjective_id (fun f => flat_of_charZero f)).2
      (isSmooth_baseProjection_schemeDeformationCategoryProjection_of_lci X hdim hsyn hfin)

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **`|Curves^{lci+}|` lies in the smooth locus.** With `hlfp` the local finite presentation of
`Curves → Spec ℤ` (Stacks 0DSS), every point of `|Curves^{lci+}|` lies in the point set of the
open substack where `Curves → Spec ℤ` is smooth, hence (Stacks 06FJ) `Curves^{lci+}` is contained
in that open substack. -/
theorem lciPlus_property_le_smoothLocus
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    {W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h)}
    (hW : Stack.IsSmoothLocus B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) W) :
    (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).property ≤ W.property := by
  refine Stack.OpenSubstack.property_le_of_pointSet_subset B integerBase hZ fun x hx => ?_
  obtain ⟨_, _, hK, X, _, hdim, hlci, hfin, q, rfl, ⟨m⟩⟩ :=
    exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus B hZ h x hx
  exact (Stack.OpenSubstack.mem_pointSet_iff B integerBase hZ _ _).2
    ⟨q, Stack.OpenSubstack.prop_of_hom B integerBase hZ _ m
      (smoothLocus_property_curvesSmallPoint_of_lci B hZ X hK hdim h hlfp hW hlci hfin), rfl⟩

/-- **Stacks 0DZX, part (1), on the stack of curves `curvesAlgebraicStack B hZ h`**, where `h` is
the algebraicity of the stack of curves (Stacks 0D5A) and `hlfp` the local finite presentation of
`Curves → Spec ℤ` (Stacks 0DSS): `Curves^{lci+} → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_lciPlus
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :
    IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_lciPlus B hZ) := by
  obtain ⟨W, hW⟩ := Stack.exists_isSmoothLocus B integerBase hZ
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
  exact Stack.OpenSubstack.isSmooth_inclusion_comp_of_le B integerBase hZ _
    (lciPlus_property_le_smoothLocus B hZ h hlfp hW) hW.1

/-- **Stacks 0E00 on the stack of curves `curvesAlgebraicStack B hZ h`**, where `h` is the
algebraicity of the stack of curves (Stacks 0D5A) and `hlfp` the local finite presentation of
`Curves → Spec ℤ` (Stacks 0DSS): `Curves^{nodal} → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_nodal
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :
    IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isAtWorstNodal B hZ) :=
  isSmoothOverIntegers_nodal_of_lciPlus B hZ h (isSmoothOverIntegers_lciPlus B hZ h hlfp)

/-- **Stacks 0E79 for `𝓜̄`, on the stack of curves `curvesAlgebraicStack B hZ h`**, where `h` is
the algebraicity of the stack of curves (Stacks 0D5A) and `hlfp` the local finite presentation of
`Curves → Spec ℤ` (Stacks 0DSS): for the open substack `𝓜̄ = Curves^{stable}` (`hst`, Stacks 0E76),
`𝓜̄ → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_stable
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ)) :
    IsSmoothOverIntegers B hZ h hst :=
  isSmoothOverIntegers_stable_of_nodal B hZ h hst (isSmoothOverIntegers_nodal B hZ h hlfp)

/-- **Stacks 0E79 for `𝓜̄_g`, on the stack of curves `curvesAlgebraicStack B hZ h`**, where `h` is
the algebraicity of the stack of curves (Stacks 0D5A) and `hlfp` the local finite presentation of
`Curves → Spec ℤ` (Stacks 0DSS): for the open substack `𝓜̄_g` of stable curves of genus `g`
(`hst`, Stacks 0E78), `𝓜̄_g → Spec(ℤ)` is smooth. -/
theorem isSmoothOverIntegers_stableOfGenus
    (hlfp : Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (g : ℕ) (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g)) :
    IsSmoothOverIntegers B hZ h hst :=
  isSmoothOverIntegers_stableOfGenus_of_nodal B hZ h g hst (isSmoothOverIntegers_nodal B hZ h hlfp)

end AlgebraicGeometry

end
