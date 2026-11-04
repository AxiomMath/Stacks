module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg

/-!
# The component restriction of a proper morphism, and its degree

The proof of Stacks 02SU reduces the projection formula
`p_*(c₁(p^*L) ∩ α) = c₁(L) ∩ p_*α` to the case of a single integral component by pushing
forward along `⨿ W_i ⟶ X`, and then settles that case by Stacks 02ST, which computes the
pushforward of a divisor cycle along a proper dominant morphism of *integral* schemes of equal
delta-dimension. `StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward` carries out the
reduction and carries the integral-component case as the hypothesis
`Stacks.Chow.FirstChernCapCompatibleWithPushforward`. This file supplies the two things standing
between that hypothesis and the first displayed equation of Stacks 02ST, which is proved in
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicDivisorPushforward`.

## The morphism between integral components

The integral closed subscheme `W = closure {x} ⊆ X` is carried by `p` into
`W' = closure {p x} ⊆ Y`, so `p` restricts to `W ⟶ W'`. Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` builds that restriction from the
containment of ideal sheaves, and the containment is an equality here
(`Stacks.Chow.map_integralComponentAt`). The restriction is dominant, and proper when `p` is.
This is the morphism the source obtains from its disjoint-union diagram, available here without
forming any disjoint union.

## The two spellings of the multiplicity, and the join between them

Stacks 02ST and Stacks 02RT state their pushforward formulas with the multiplicity
`[R(X) : R(Y)]`, the degree of the extension of function fields; the pushforward of cycles of
Stacks 02R4 — and hence `Stacks.Chow.pushforwardWeight` — is defined with
`AlgebraicGeometry.Scheme.Hom.residueDegree`, the degree of the residue field extension at a
point. `Stacks.Chow.finrank_functionField_eq_residueDegree` identifies the two for a dominant
morphism of integral schemes: the function field of an integral scheme *is* the residue field of
its generic point, the stalk there being a field already, and under that identification
`AlgebraicGeometry.dominantFunctionFieldMap` is the residue field map at the generic point.
Specialised to the component restriction and combined with the multiplicativity of the residue
degree along the two closed immersions, this says that the weight with which `x` enters the
proper pushforward is `[R(W) : R(W')]`
(`Stacks.Chow.pushforwardWeight_eq_finrank_functionField`).

## Main definitions

* `Stacks.Chow.integralComponentMap` — the restriction of a morphism to the integral component
  of a point.
* `Stacks.Chow.functionFieldEquivResidueField` — on an integral scheme, the function field is
  the residue field of the generic point.

## Main results

* `Stacks.Chow.integralComponentMap_subschemeι`,
  `Stacks.Chow.isDominant_integralComponentMap`, `Stacks.Chow.isProper_integralComponentMap` —
  the component restriction commutes with the closed immersions, and is dominant, and proper.
* `Stacks.Chow.finrank_functionField_eq_residueDegree` — the degree of the extension of function
  fields of a dominant morphism of integral schemes is its residue degree at the generic point.
* `Stacks.Chow.pushforwardWeight_eq_finrank_functionField` — the same identity in the vocabulary
  of Stacks 02SU: the pushforward weight at a point where the relative dimension is preserved is
  the degree of the extension of the function fields of the two integral components.
* `Stacks.Chow.properPushforward_firstChernComponentCycleAt` — the pushforward of a component
  cycle factors through the component restriction. Both steps are Stacks 02R5.
* `Stacks.Chow.firstChernCapCompatibleWithPushforward_of_integralComponentMap` — the
  integral-component hypothesis of Stacks 02SU, reduced to a statement about the component
  restriction alone.

## Implementation notes

### What the reduction does and does not supply

`Stacks.Chow.firstChernCapCompatibleWithPushforward_of_integralComponentMap` takes two
hypotheses, and they are not on the same footing.

The first is the dimension-*preserving* case, and it is exactly the shape of the first displayed
equation of Stacks 02ST: for a point `x` whose relative dimension is `k + 1` and whose image has
relative dimension `k + 1` as well, the pushforward along `W ⟶ W'` of the value of the rule on
`W` is `[R(W) : R(W')]` times its value on `W'` — the multiplicity being
`Stacks.Chow.pushforwardWeight`, which
`Stacks.Chow.pushforwardWeight_eq_finrank_functionField` rewrites into the function-field degree
that `Stacks.Chow.properPushforward_meromorphicDivisorCycle` produces. So in that case nothing
is left but to substitute a rule built from an invertible module, which is Stacks 02SJ and is
not in this repository.

The second is the dimension-*dropping* case, and it is **a restriction of the conclusion, not a
reduction of it**: it asks outright that the pushforward of the component cycle vanish when the
image component has smaller delta-dimension. It is stated as a hypothesis rather than proved
because the component rule here is an arbitrary
`Stacks.Chow.FirstChernComponentCycleRule`, and nothing about an arbitrary rule makes that
pushforward vanish — the source's own proof passes over this case, reducing to "`X`, `Y`
integral, `f` dominant" and then invoking Stacks 02ST, which assumes
`dim_δ(X) = dim_δ(Y)`. So this file reduces the dimension-preserving half of the
integral-component case of Stacks 02SU and leaves the dropping half exactly where the source
leaves it.

### No `@[stacks]` attribute here, and where the tags are

Nothing here is a tagged statement. The statements about the component restriction are
infrastructure; the reduction carries the component rules and both hypotheses described above.
So no `@[stacks 02SU]` and no `@[stacks 02ST]` attribute is placed in this file.

Stacks 02SU is proved for a **closed immersion** as
`Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible`: there the component
restriction is an isomorphism, so the dimension-dropping hypothesis `h0` above is vacuous and the
dimension-preserving one is settled by the first displayed equation of Stacks 02ST together with
Stacks 02SJ (2), the independence of the chosen meromorphic section. The general proper case of
Stacks 02SU is `Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_of_isProper` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper`, which carries the tag; its
dimension-dropping case is the second displayed equation of Stacks 02ST,
`Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_fundamentalCycle` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward`.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The restriction of a morphism to the integral component of a point -/

/-- The ideal sheaf of the integral component of `x` pushes forward to the ideal sheaf of the
integral component of its image: the closure of the image of the closure of `{x}` is the closure
of `{f x}`. -/
theorem map_integralComponentAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (integralComponentAt x).map f = integralComponentAt (f.base x) := by
  rw [show integralComponentAt x =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) from rfl,
    Scheme.IdealSheafData.map_vanishingIdeal]
  refine congrArg _ (Closeds.ext ?_)
  show closure (f.base '' closure ({x} : Set X)) = closure ({f.base x} : Set Y)
  refine le_antisymm (closure_minimal ?_ isClosed_closure) ?_
  · simpa using image_closure_subset_closure_image (s := ({x} : Set X)) f.continuous
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)

/-- **The restriction of `f` to the integral component of a point.** The integral closed
subscheme `closure {x} ⊆ X` is carried into `closure {f x} ⊆ Y`, so `f` restricts to a morphism
between them. In the proof of Stacks 02SU this is the morphism `W_i ⟶ W'_i` onto the image
component, which the source obtains from the disjoint-union diagram. -/
def integralComponentMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (integralComponentAt x).subscheme ⟶ (integralComponentAt (f.base x)).subscheme :=
  (integralComponentAt x).subschemeMap (integralComponentAt (f.base x)) f
    (le_of_eq (map_integralComponentAt f x).symm)

/-- The restriction of `f` to integral components commutes with the two closed immersions. -/
@[reassoc]
theorem integralComponentMap_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    integralComponentMap f x ≫ (integralComponentAt (f.base x)).subschemeι =
      (integralComponentAt x).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The restriction to integral components takes the generic point to the generic point: both
sides have the same image under the closed immersion of the target component, namely `f x`. -/
theorem integralComponentMap_base_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := isIntegral_integralComponentAt x
    letI := isIntegral_integralComponentAt (f.base x)
    (integralComponentMap f x).base (genericPoint (integralComponentAt x).subscheme) =
      genericPoint (integralComponentAt (f.base x)).subscheme := by
  have := isIntegral_integralComponentAt x
  have := isIntegral_integralComponentAt (f.base x)
  refine (integralComponentAt (f.base x)).subschemeι.isClosedEmbedding.injective ?_
  show (integralComponentMap f x ≫ (integralComponentAt (f.base x)).subschemeι).base
    (genericPoint (integralComponentAt x).subscheme) = _
  rw [integralComponentMap_subschemeι]
  exact (congrArg f.base (genericPointOf_integralComponentAt x)).trans
    (genericPointOf_integralComponentAt (f.base x)).symm

/-- The restriction to integral components is dominant: its source is the closure of a point
whose image is the generic point of the target. -/
instance isDominant_integralComponentMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    IsDominant (integralComponentMap f x) := by
  have := isIntegral_integralComponentAt x
  have := isIntegral_integralComponentAt (f.base x)
  exact ((tfae_isDominant_of_isIntegral (integralComponentMap f x)).out 1 2).mpr
    (integralComponentMap_base_genericPoint f x)

/-- The restriction of a proper morphism to integral components is proper: composed with the
closed immersion of the target component it is the closed immersion of the source component
followed by `p`, hence proper, and a closed immersion is separated. -/
instance isProper_integralComponentMap {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (x : X) :
    IsProper (integralComponentMap p x) := by
  have h : IsProper (integralComponentMap p x ≫
      (integralComponentAt (p.base x)).subschemeι) := by
    rw [integralComponentMap_subschemeι]; infer_instance
  exact IsProper.of_comp _ (integralComponentAt (p.base x)).subschemeι

/-! ### The function field as the residue field of the generic point -/

/-- **On an integral scheme the function field is the residue field of the generic point.** The
stalk at the generic point is already a field, so the residue map is injective, and it is always
surjective. -/
def functionFieldEquivResidueField (X : Scheme.{u}) [IsIntegral X] :
    X.functionField ≃+* X.residueField (genericPoint X) :=
  RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective (genericPoint X)⟩

/-- **The naturality square of the residue map against a stalk map transported along an equality
of base points.** This is what identifies the extension of function fields of a dominant morphism
with its residue field map at the generic point. -/
theorem residue_stalkMap_transport {X S : Scheme.{u}} (f : X ⟶ S) (x : X) {y : S}
    (h : f.base x = y) (a : S.presheaf.stalk y) :
    X.residue x ((h ▸ f.stalkMap x).hom a) =
      f.residueFieldMap x ((S.residueFieldCongr h).inv (S.residue y a)) := by
  cases h
  have hnat := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  simp [← hnat]

/-! ### The degree of the function field extension is the residue degree -/

/-- **The degree of the extension of function fields of a dominant morphism of integral schemes
is its residue degree at the generic point.** This is the join between the multiplicity
`[R(X) : R(Y)]` in which Stacks 02ST and Stacks 02RT state their pushforward formulas and the
multiplicity `AlgebraicGeometry.Scheme.Hom.residueDegree` in which the pushforward of cycles of
Stacks 02R4 — and so `Stacks.Chow.pushforwardWeight` — is defined. The two function fields are
the residue fields of the generic points, and under that identification
`AlgebraicGeometry.dominantFunctionFieldMap` is the residue field map. -/
theorem finrank_functionField_eq_residueDegree {W W' : Scheme.{u}} [IsIntegral W] [IsIntegral W']
    (r : W ⟶ W') [IsDominant r] :
    letI : Algebra W'.functionField W.functionField := (dominantFunctionFieldMap r).toAlgebra
    Module.finrank W'.functionField W.functionField = r.residueDegree (genericPoint W) := by
  have hgen : r.base (genericPoint W) = genericPoint W' :=
    Stacks.Divisors.base_genericPoint_of_isDominant r
  let _ : Algebra W'.functionField W.functionField := (dominantFunctionFieldMap r).toAlgebra
  let _ : Algebra (W'.residueField (r.base (genericPoint W))) (W.residueField (genericPoint W)) :=
    (r.residueFieldMap (genericPoint W)).hom.toAlgebra
  let i : W'.functionField ≃+* W'.residueField (r.base (genericPoint W)) :=
    (functionFieldEquivResidueField W').trans
      (W'.residueFieldCongr hgen).commRingCatIsoToRingEquiv.symm
  refine Algebra.finrank_eq_of_equiv_equiv i (functionFieldEquivResidueField W) ?_
  ext a
  exact (residue_stalkMap_transport r (genericPoint W) hgen a).symm

/-- The residue degree of the restriction of `p` to the integral component of `x`, at the generic
point of that component, is the residue degree of `p` at `x`: the two closed immersions
contribute degree one and the residue degree is multiplicative. -/
theorem residueDegree_integralComponentMap {X Y : Scheme.{u}} (p : X ⟶ Y) (x : X) :
    letI := isIntegral_integralComponentAt x
    (integralComponentMap p x).residueDegree
        (genericPoint (integralComponentAt x).subscheme) = p.residueDegree x := by
  have := isIntegral_integralComponentAt x
  have h := congrArg
    (fun φ : (integralComponentAt x).subscheme ⟶ Y ↦
      φ.residueDegree (genericPoint (integralComponentAt x).subscheme))
    (integralComponentMap_subschemeι p x)
  simp only [residueDegree_comp, residueDegree_eq_one_of_isClosedImmersion, one_mul,
    mul_one] at h
  rw [h]
  exact congrArg p.residueDegree (genericPointOf_integralComponentAt x)

/-- **The residue degree of `p` at `x` is the degree of the extension of the function fields of
the integral components through `x` and through `p x`.** This is the form in which the
multiplicity of Stacks 02ST enters the projection formula of Stacks 02SU. -/
theorem finrank_functionField_integralComponent {X Y : Scheme.{u}} (p : X ⟶ Y) (x : X) :
    letI := isIntegral_integralComponentAt x
    letI := isIntegral_integralComponentAt (p.base x)
    letI : Algebra (integralComponentAt (p.base x)).subscheme.functionField
        (integralComponentAt x).subscheme.functionField :=
      (dominantFunctionFieldMap (integralComponentMap p x)).toAlgebra
    Module.finrank (integralComponentAt (p.base x)).subscheme.functionField
        (integralComponentAt x).subscheme.functionField = p.residueDegree x := by
  have := isIntegral_integralComponentAt x
  have := isIntegral_integralComponentAt (p.base x)
  exact (finrank_functionField_eq_residueDegree (integralComponentMap p x)).trans
    (residueDegree_integralComponentMap p x)

/-- **The pushforward weight of Stacks 02R4 is the degree of the extension of function fields of
the integral components**, at a point where the morphism preserves the relative dimension. This
is the join the proof of Stacks 02SU needs: it turns the weight appearing in
`Stacks.Chow.FirstChernCapCompatibleWithPushforward` into the multiplicity
`[R(W) : R(W')]` that the first displayed equation of Stacks 02ST produces. -/
theorem pushforwardWeight_eq_finrank_functionField (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) (x : X)
    (hdim : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (p.base x)) :
    letI := isIntegral_integralComponentAt x
    letI := isIntegral_integralComponentAt (p.base x)
    letI : Algebra (integralComponentAt (p.base x)).subscheme.functionField
        (integralComponentAt x).subscheme.functionField :=
      (dominantFunctionFieldMap (integralComponentMap p x)).toAlgebra
    pushforwardWeight C sX sY p x =
      (Module.finrank (integralComponentAt (p.base x)).subscheme.functionField
        (integralComponentAt x).subscheme.functionField : ℤ) := by
  have := isIntegral_integralComponentAt x
  have := isIntegral_integralComponentAt (p.base x)
  let _ : Algebra (integralComponentAt (p.base x)).subscheme.functionField
      (integralComponentAt x).subscheme.functionField :=
    (dominantFunctionFieldMap (integralComponentMap p x)).toAlgebra
  rw [show (Module.finrank (integralComponentAt (p.base x)).subscheme.functionField
      (integralComponentAt x).subscheme.functionField : ℤ) = (p.residueDegree x : ℤ) from
    congrArg _ (finrank_functionField_integralComponent p x)]
  simp [pushforwardWeight, AlgebraicCycle.mapCoeff, hdim]

/-! ### Reducing Stacks 02SU on integral components to the component restriction -/

/-- The delta-dimension of the integral component of a point of relative dimension `k + 1`. -/
theorem schemeDeltaDimension_integralComponentAt_of_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] {x : X} {k : ℤ}
    (hx : relativeDimension C.dimensionFunction q x = k + 1) :
    schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ q) = ((k + 1 : ℤ) : EInt) := by
  rw [schemeDeltaDimension_integralComponentAt, hx]

/-- At a point of relative dimension `k + 1` the point-indexed component cycle is the component
cycle of the integral component through that point. -/
theorem firstChernComponentCycleAt_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (k : ℤ) (chern : FirstChernComponentCycleRule C q k) {x : X}
    (hx : relativeDimension C.dimensionFunction q x = k + 1) :
    firstChernComponentCycleAt C q k chern x =
      firstChernComponentCycle C q k chern (integralComponentAt x)
        (isIntegral_integralComponentAt x)
        (schemeDeltaDimension_integralComponentAt_of_eq C q hx) :=
  Subtype.ext ((firstChernCapRule C q k chern).totalize_eq _ _ _)

/-- The restriction of `p` to the integral component of `x` is a morphism over the base. -/
theorem integralComponentMap_comp_base (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) (sY : Y ⟶ C.S) (p : X ⟶ Y) (hp : p ≫ sY = sX) (x : X) :
    integralComponentMap p x ≫ ((integralComponentAt (p.base x)).subschemeι ≫ sY) =
      (integralComponentAt x).subschemeι ≫ sX := by
  rw [integralComponentMap_subschemeι_assoc, hp]

section Reduction

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
  (chernX : FirstChernComponentCycleRule C sX k) (chernY : FirstChernComponentCycleRule C sY k)

include hp in
/-- **The pushforward of a component cycle factors through the component restriction.** The
component cycle at a point `x` of relative dimension `k + 1` is the pushforward to `X` of the
value of the rule on `W = closure {x}`; pushing that forward to `Y` is the same as pushing it
along `W ⟶ W'` and then along the closed immersion of `W' = closure {p x}`, because the two
composites `W ⟶ Y` agree. Both steps are Stacks 02R5. -/
theorem properPushforward_firstChernComponentCycleAt {x : X}
    (hx : relativeDimension C.dimensionFunction sX x = k + 1) :
    properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x) =
      properPushforward C ((integralComponentAt (p.base x)).subschemeι ≫ sY) sY
        (integralComponentAt (p.base x)).subschemeι rfl k
        (properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
          ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
          (integralComponentMap_comp_base C sX sY p hp x) k
          (chernX (integralComponentAt x) (isIntegral_integralComponentAt x)
            (schemeDeltaDimension_integralComponentAt_of_eq C sX hx))) := by
  rw [firstChernComponentCycleAt_eq C sX k chernX hx]
  exact (congrFun (properPushforward_comp C _ sX sY _ p rfl hp k) _).trans
    ((congrFun (properPushforward_congr C _ sY _ _ (integralComponentMap_subschemeι p x).symm
      _ _ k) _).trans
      (congrFun (properPushforward_comp C _ _ sY (integralComponentMap p x) _
        (integralComponentMap_comp_base C sX sY p hp x) rfl k) _).symm)

include hp in
/-- `Stacks.Chow.FirstChernCapCompatibleWithPushforward` holds provided that, for every point `x`
of relative dimension `k + 1` whose image `p x` also has relative dimension `k + 1`, pushing the
value of the rule on `W = closure {x}` forward along `W ⟶ W' = closure {p x}` gives
`pushforwardWeight C sX sY p x` times the value of the rule on `W'`, and that the component cycle
at every point of relative dimension `k + 1` whose image has a different relative dimension
pushes forward to zero. -/
theorem firstChernCapCompatibleWithPushforward_of_integralComponentMap
    (h : ∀ (x : X) (hx : relativeDimension C.dimensionFunction sX x = k + 1)
      (hy : relativeDimension C.dimensionFunction sY (p.base x) = k + 1),
      properPushforward C ((integralComponentAt x).subschemeι ≫ sX)
          ((integralComponentAt (p.base x)).subschemeι ≫ sY) (integralComponentMap p x)
          (integralComponentMap_comp_base C sX sY p hp x) k
          (chernX (integralComponentAt x) (isIntegral_integralComponentAt x)
            (schemeDeltaDimension_integralComponentAt_of_eq C sX hx)) =
        pushforwardWeight C sX sY p x •
          chernY (integralComponentAt (p.base x)) (isIntegral_integralComponentAt (p.base x))
            (schemeDeltaDimension_integralComponentAt_of_eq C sY hy))
    (h0 : ∀ x : X, relativeDimension C.dimensionFunction sX x = k + 1 →
      relativeDimension C.dimensionFunction sY (p.base x) ≠ k + 1 →
      properPushforward C sX sY p hp k (firstChernComponentCycleAt C sX k chernX x) = 0) :
    FirstChernCapCompatibleWithPushforward C sX sY p hp k chernX chernY := by
  intro x hx y
  by_cases hy : relativeDimension C.dimensionFunction sY (p.base x) = k + 1
  · rw [properPushforward_firstChernComponentCycleAt C sX sY p hp k chernX hx, h x hx hy,
      firstChernComponentCycleAt_eq C sY k chernY hy]
    rw [show properPushforward C ((integralComponentAt (p.base x)).subschemeι ≫ sY) sY
        (integralComponentAt (p.base x)).subschemeι rfl k
        (pushforwardWeight C sX sY p x •
          chernY (integralComponentAt (p.base x)) (isIntegral_integralComponentAt (p.base x))
            (schemeDeltaDimension_integralComponentAt_of_eq C sY hy)) =
        pushforwardWeight C sX sY p x •
          properPushforward C ((integralComponentAt (p.base x)).subschemeι ≫ sY) sY
            (integralComponentAt (p.base x)).subschemeι rfl k
            (chernY (integralComponentAt (p.base x))
              (isIntegral_integralComponentAt (p.base x))
              (schemeDeltaDimension_integralComponentAt_of_eq C sY hy)) from
      map_zsmul (properPushforwardHom C ((integralComponentAt (p.base x)).subschemeι ≫ sY) sY
        (integralComponentAt (p.base x)).subschemeι rfl k) _ _]
    rfl
  · rw [h0 x hx hy, pushforwardWeight_eq_zero C sX sY p
      (fun heq ↦ hy (heq.symm.trans hx))]
    simp

end Reduction

end Stacks.Chow

end
