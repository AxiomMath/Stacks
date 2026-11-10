module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg

/-!
# The generic fibre of a dominant morphism of integral schemes, as a curve over a field

Let `p : X ⟶ Y` be a morphism of schemes with `X` integral, let `η` be the generic point of `X`
and let `b = p(η)`. The scheme-theoretic fibre `p.fiber b` of `AlgebraicGeometry.Scheme.Hom.fiber`
*is* the base change of `p` along `Spec κ(b) ⟶ Y`, so no new construction is needed to exhibit
the generic fibre as a base change. What this file adds is what the Chow-theoretic use of it
needs:

* the fibre is irreducible, with the image `p.asFiber η` of `η` as its generic point;
* the reduced induced structure on it — `Stacks.Chow.genericFibreCurve`, the integral closed
  subscheme attached to that generic point — is an integral scheme, proper and locally of finite
  type over `Spec κ(b)` when `p` is proper and locally of finite type, and its inclusion into
  `X` is a dominant preimmersion with image the set-theoretic fibre `p ⁻¹' {b}`;
* its delta-dimension over the Chow situation `Stacks.Chow.fieldChowSituation κ(b)` is the
  residue transcendence degree of `p` at `η`.

The last point is proved by a cancellation rather than by a dimension formula: in the cartesian
square defining the fibre, the horizontal sides `p.fiber b ⟶ X` and `Spec κ(b) ⟶ Y` are both
preimmersions, so by `Stacks.Chow.residueTrdeg_eq_of_comp_eq_comp` the residue transcendence
degrees of the two vertical sides agree. Since the base dimension function of
`Stacks.Chow.fieldChowSituation` vanishes, the delta-dimension of the generic fibre is that
transcendence degree. When `p` is dominant and the delta-dimensions of `X` and `Y` are `n` and
`n - 1`, the degree is one — that is `Stacks.Chow.schemeDeltaDimension_genericFibreCurve_eq_one`,
which says the generic fibre is a curve over the function field of `Y`.

## Main definitions

* `Stacks.Chow.genericFibreCurve` — the reduced induced structure on the generic fibre, as a
  closed subscheme of `p.fiber (p η)`.
* `Stacks.Chow.genericFibreCurveι` — its inclusion into `X`.
* `Stacks.Chow.genericFibreSpecMap` — the fibre's own structure morphism to `Spec κ(p η)`.
* `Stacks.Chow.genericFibreFromSpec` — the canonical morphism `Spec κ(p η) ⟶ Y`.
* `Stacks.Chow.genericFibreCurveToSpec` — the curve's structure morphism to `Spec κ(p η)`.

## Main results

* `Stacks.Chow.isGenericPoint_asFiber_genericPoint` and
  `Stacks.Chow.irreducibleSpace_fiber_image_genericPoint` — the generic fibre is irreducible with
  generic point `p.asFiber η`.
* `Stacks.Chow.range_genericFibreCurveι` — the inclusion has image the set-theoretic fibre.
* `Stacks.Chow.isDominant_genericFibreCurveι` — the inclusion is dominant, because the fibre
  contains `η`.
* `Stacks.Chow.residueTrdeg_fiberToSpecResidueField_asFiber` — the residue transcendence degree
  of the fibre's structure morphism at the generic point equals that of `p` at `η`.
* `Stacks.Chow.schemeDeltaDimension_genericFibreCurve` and
  `Stacks.Chow.schemeDeltaDimension_genericFibreCurve_eq_one` — the delta-dimension of the
  generic fibre over `Spec κ(p η)`, and the fact that it is one in the dimension-drop case.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section Topology

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIntegral X]

/-- The image of the generic point of `X` in the fibre of `p` over `p(η)` is a generic point of
that fibre: the inclusion of the fibre is an embedding, and `η` specializes to every point of
`X`. -/
theorem isGenericPoint_asFiber_genericPoint :
    IsGenericPoint (p.asFiber (genericPoint X))
      (Set.univ : Set (p.fiber (p.base (genericPoint X)))) := by
  refine isGenericPoint_iff_specializes.mpr fun z ↦ iff_of_true ?_ (Set.mem_univ z)
  refine (p.fiberι (p.base (genericPoint X))).isEmbedding.isInducing.specializes_iff.mp ?_
  rw [Scheme.Hom.fiberι_asFiber]
  exact genericPoint_specializes _

/-- The fibre of `p` over the image of the generic point of an integral `X` is irreducible. -/
instance irreducibleSpace_fiber_image_genericPoint :
    IrreducibleSpace (p.fiber (p.base (genericPoint X))) := by
  have h := isGenericPoint_asFiber_genericPoint p
  rw [irreducibleSpace_def, Set.top_eq_univ, ← isGenericPoint_def.mp h]
  exact isIrreducible_singleton.closure

/-- The image of the generic point of `X` is *the* generic point of the fibre. -/
theorem asFiber_genericPoint :
    p.asFiber (genericPoint X) = genericPoint (p.fiber (p.base (genericPoint X))) :=
  (isGenericPoint_asFiber_genericPoint p).eq (genericPoint_spec _)

end Topology

section Curve

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIntegral X]

/-- The structure morphism `p.fiber (p η) ⟶ Spec κ(p η)` of the generic fibre, typed over the
base of `Stacks.Chow.fieldChowSituation` at that residue field rather than over `Spec` of it.

The two targets are the same scheme by `rfl`, but `Stacks.Chow.schemeDeltaDimension` takes a
morphism into the base of a Chow situation and requires its `LocallyOfFiniteType` instance at
*that* spelling; an instance declared at the other spelling is not found. So the spelling is
fixed once here and every declaration below uses it. -/
def genericFibreSpecMap :
    p.fiber (p.base (genericPoint X)) ⟶
      (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).S :=
  p.fiberToSpecResidueField (p.base (genericPoint X))

/-- The structure morphism of the generic fibre is proper when `p` is proper. -/
instance isProper_genericFibreSpecMap [IsProper p] : IsProper (genericFibreSpecMap p) :=
  inferInstanceAs (IsProper (pullback.snd p (Y.fromSpecResidueField (p.base (genericPoint X)))))

/-- The structure morphism of the generic fibre is locally of finite type when `p` is. -/
instance locallyOfFiniteType_genericFibreSpecMap [LocallyOfFiniteType p] :
    LocallyOfFiniteType (genericFibreSpecMap p) :=
  inferInstanceAs
    (LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField (p.base (genericPoint X)))))

/-- The canonical morphism `Spec κ(p η) ⟶ Y`, with its source written as the base of
`Stacks.Chow.fieldChowSituation`, for the same reason as
`Stacks.Chow.genericFibreSpecMap`. -/
def genericFibreFromSpec :
    (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).S ⟶ Y :=
  Y.fromSpecResidueField (p.base (genericPoint X))

/-- The canonical morphism `Spec κ(p η) ⟶ Y` is a preimmersion. -/
instance isPreimmersion_genericFibreFromSpec : IsPreimmersion (genericFibreFromSpec p) :=
  inferInstanceAs (IsPreimmersion (Y.fromSpecResidueField (p.base (genericPoint X))))

/-- **The fibre square.** The inclusion of the fibre followed by `p` is the fibre's structure
morphism followed by `Spec κ(p η) ⟶ Y`; this is
`AlgebraicGeometry.Scheme.Hom.fiber_fac` at the spelling used here. -/
theorem genericFibreSpecMap_fac :
    p.fiberι (p.base (genericPoint X)) ≫ p = genericFibreSpecMap p ≫ genericFibreFromSpec p :=
  p.fiber_fac _

/-- The residue transcendence degree of `Stacks.Chow.genericFibreSpecMap` is that of the fibre's
own structure morphism: the two are the same morphism, written over two spellings of one
scheme. -/
theorem residueTrdeg_genericFibreSpecMap (z : p.fiber (p.base (genericPoint X))) :
    residueTrdeg (genericFibreSpecMap p) z =
      residueTrdeg (p.fiberToSpecResidueField (p.base (genericPoint X))) z :=
  rfl

/-- **The generic fibre of `p` as an integral scheme**: the reduced induced structure on the
fibre of `p` over the image of the generic point of `X`, which is irreducible, so this is the
integral closed subscheme attached to its generic point. -/
def genericFibreCurve : (p.fiber (p.base (genericPoint X))).IdealSheafData :=
  integralComponentAt (p.asFiber (genericPoint X))

/-- The generic fibre curve is the integral closed subscheme attached to the generic point of the
fibre. -/
theorem genericFibreCurve_def :
    genericFibreCurve p = integralComponentAt (p.asFiber (genericPoint X)) :=
  rfl

/-- The generic fibre curve is an integral scheme. -/
instance isIntegral_genericFibreCurve : IsIntegral (genericFibreCurve p).subscheme :=
  isIntegral_integralComponentAt _

/-- The generic point of the generic fibre curve is the image of the generic point of `X`. -/
theorem genericPointOf_genericFibreCurve :
    genericPointOf (genericFibreCurve p) (isIntegral_genericFibreCurve p) =
      p.asFiber (genericPoint X) :=
  genericPointOf_integralComponentAt _

/-- The inclusion of the generic fibre curve into `X`. -/
def genericFibreCurveι : (genericFibreCurve p).subscheme ⟶ X :=
  (genericFibreCurve p).subschemeι ≫ p.fiberι (p.base (genericPoint X))

/-- The inclusion of the generic fibre curve into `X` is the inclusion of the reduced structure
followed by the inclusion of the fibre. -/
theorem genericFibreCurveι_def :
    genericFibreCurveι p =
      (genericFibreCurve p).subschemeι ≫ p.fiberι (p.base (genericPoint X)) :=
  rfl

/-- The structure morphism of the generic fibre curve over the residue field at `p(η)`. -/
def genericFibreCurveToSpec :
    (genericFibreCurve p).subscheme ⟶
      (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).S :=
  (genericFibreCurve p).subschemeι ≫ genericFibreSpecMap p

/-- The structure morphism of the generic fibre curve is the fibre's structure morphism
precomposed with the inclusion of the reduced structure. -/
theorem genericFibreCurveToSpec_def :
    genericFibreCurveToSpec p = (genericFibreCurve p).subschemeι ≫ genericFibreSpecMap p :=
  rfl

/-- The inclusion of the generic fibre curve into `X` is a preimmersion. -/
instance isPreimmersion_genericFibreCurveι : IsPreimmersion (genericFibreCurveι p) := by
  rw [genericFibreCurveι_def]
  infer_instance

/-- The generic fibre curve is proper over `Spec κ(p η)` when `p` is proper. -/
instance isProper_genericFibreCurveToSpec [IsProper p] :
    IsProper (genericFibreCurveToSpec p) := by
  rw [genericFibreCurveToSpec_def]
  infer_instance

/-- The generic fibre curve is locally of finite type over `Spec κ(p η)` when `p` is locally of
finite type. -/
instance locallyOfFiniteType_genericFibreCurveToSpec [LocallyOfFiniteType p] :
    LocallyOfFiniteType (genericFibreCurveToSpec p) := by
  rw [genericFibreCurveToSpec_def]
  infer_instance

/-- **The fibre square for the generic fibre curve.** -/
theorem genericFibreCurveι_fac :
    genericFibreCurveι p ≫ p = genericFibreCurveToSpec p ≫ genericFibreFromSpec p := by
  rw [genericFibreCurveι_def, genericFibreCurveToSpec_def, Category.assoc, Category.assoc,
    genericFibreSpecMap_fac]

/-- **The generic fibre curve has the set-theoretic fibre as its image.** The reduced induced
structure is supported on the whole fibre, and the fibre of
`AlgebraicGeometry.Scheme.Hom.fiber` has the set-theoretic fibre as its range. -/
theorem range_genericFibreCurveι :
    Set.range (genericFibreCurveι p) = p.base ⁻¹' {p.base (genericPoint X)} := by
  have hsupp : Set.range (genericFibreCurve p).subschemeι.base = Set.univ := by
    rw [Scheme.IdealSheafData.range_subschemeι, genericFibreCurve_def,
      coe_support_integralComponentAt, ← isGenericPoint_def.mp
        (isGenericPoint_asFiber_genericPoint p)]
  change Set.range ((p.fiberι (p.base (genericPoint X))).base ∘
    (genericFibreCurve p).subschemeι.base) = _
  rw [Set.range_comp, hsupp, Set.image_univ, Scheme.Hom.range_fiberι]

/-- **The inclusion of the generic fibre curve into `X` is dominant.** Its image is the fibre
through the generic point of `X`, whose closure is all of `X`. -/
instance isDominant_genericFibreCurveι : IsDominant (genericFibreCurveι p) := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range, range_genericFibreCurveι]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← genericPoint_closure X]
  exact closure_mono (by simp)

end Curve

/-! ### The delta-dimension of the generic fibre -/

section Dimension

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIntegral X]

/-- **The residue transcendence degree of the fibre is that of `p`.** The defining square of the
fibre has `p.fiber b ⟶ X` and `Spec κ(b) ⟶ Y` as its horizontal sides and both are
preimmersions, so `Stacks.Chow.residueTrdeg_eq_of_comp_eq_comp` cancels them. -/
theorem residueTrdeg_fiberToSpecResidueField_asFiber :
    residueTrdeg (p.fiberToSpecResidueField (p.base (genericPoint X)))
        (p.asFiber (genericPoint X)) = residueTrdeg p (genericPoint X) := by
  have h := residueTrdeg_eq_of_comp_eq_comp (p.fiberι (p.base (genericPoint X))) p
    (p.fiberToSpecResidueField (p.base (genericPoint X)))
    (Y.fromSpecResidueField (p.base (genericPoint X)))
    (p.fiber_fac (p.base (genericPoint X))) (p.asFiber (genericPoint X))
  rw [Scheme.Hom.fiberι_asFiber] at h
  exact h.symm

/-- **The delta-dimension of the generic fibre curve over the residue field at `p(η)`** is the
residue transcendence degree of `p` at the generic point of `X`. The base dimension function of
`Stacks.Chow.fieldChowSituation` vanishes, so the delta-dimension is the residue transcendence
degree of the fibre's structure morphism, which is that of `p` by
`Stacks.Chow.residueTrdeg_fiberToSpecResidueField_asFiber`. -/
theorem schemeDeltaDimension_genericFibreCurve [LocallyOfFiniteType p] :
    schemeDeltaDimension (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X))))
        (genericFibreCurveToSpec p) =
      ((Cardinal.toNat (residueTrdeg p (genericPoint X)) : ℤ) : EInt) := by
  have h := schemeDeltaDimension_integralComponentAt
    (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X))))
    (genericFibreSpecMap p) (p.asFiber (genericPoint X))
  rw [relativeDimension_apply_add_residueTrdeg, fieldChowSituation_dimensionFunction,
    residueTrdeg_genericFibreSpecMap, residueTrdeg_fiberToSpecResidueField_asFiber, zero_add] at h
  exact h

/-- **The generic fibre is a curve over the residue field at `p(η)`** when `p` is dominant, `X`
has delta-dimension `n` and `Y` has delta-dimension `n - 1`. The residue transcendence degree of
`p` at the generic point is then one, because the relative dimension of a composite grows by
exactly that degree and the generic point of `X` lies over the generic point of `Y`. -/
theorem schemeDeltaDimension_genericFibreCurve_eq_one (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral Y] [LocallyOfFiniteType p] [IsDominant p] (hp : p ≫ sY = sX) {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = ((n - 1 : ℤ) : EInt)) :
    schemeDeltaDimension (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X))))
      (genericFibreCurveToSpec p) = (1 : EInt) := by
  have hgen : p.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have hXrel : relativeDimension C.dimensionFunction sX (genericPoint X) = n :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sX).symm.trans hnX)
  have hYrel : relativeDimension C.dimensionFunction sY (genericPoint Y) = n - 1 :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sY).symm.trans hnY)
  have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY p (genericPoint X)
  rw [hp, hgen, hXrel, hYrel] at hstep
  rw [schemeDeltaDimension_genericFibreCurve p,
    show Cardinal.toNat (residueTrdeg p (genericPoint X)) = 1 from by omega]
  rfl

end Dimension

end Stacks.Chow

end
