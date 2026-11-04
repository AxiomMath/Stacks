module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BaseChangeComponentDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity of the base-change map on cycle groups

Let `B` be a flat base change of Chow situations whose base-change morphism `g : S' ⟶ S` is
surjective on points. For `X` locally of finite type over `S` the induced homomorphism
`Z_k(X) ⟶ Z_{k+c}(X ×_S S')` on cycle groups is injective.

The reason is that a point `x` of `X` carrying a nonzero coefficient is hit by a point of
`X ×_S S'` which is the image of a generic point of the scheme-theoretic inverse image of the
reduced closure of `x`. At such a point the multiplicity entering the base-changed cycle is the
length of a nonzero module of finite length, hence nonzero, and the relative dimension is the
delta-dimension of a component of the base change of the reduced closure of `x`, hence the
correct one; so the coefficient of the base-changed cycle there is a product of two nonzero
integers.

The case of interest is an arbitrary extension `K/k` of fields: the spectrum of a field is a
single point, so `Spec K ⟶ Spec k` is surjective, and the base-change map
`Z_r(X) ⟶ Z_r(X_K)` on cycles of an algebraic scheme over `k` is injective. That map, together
with its injectivity, is the content of Section 0H4E outside its two lemmas 0H4F and 0H4G, and
is what `Stacks.Chow.injective_baseChangeCyclePullback_fieldExtension` carries.

## Main results

* `Stacks.Chow.eq_zero_of_baseChangeCyclePullback_eq_zero_of_mem_range` — a cycle whose base
  change vanishes has coefficient zero at every point in the image of the base change.
* `Stacks.Chow.injective_baseChangeCyclePullback_of_surjective` — injectivity of the
  base-change map for a surjective flat change of the base scheme.
* `Stacks.Chow.injective_baseChangeCyclePullback_fieldExtension` — injectivity of
  `Z_r(X) ⟶ Z_r(X_K)` for an arbitrary extension of fields.

## Implementation notes

No hypothesis is placed on the fibres of `g`: the existing injectivity statement of
`StacksFrontier.AlgebraicGeometry.Chow.PerfectClosureCycles` assumes the projections of the base
change to be homeomorphisms, which holds for a purely inseparable extension but fails for a
general field extension. What survives in general is the weaker statement that the projection
is surjective, and that is all injectivity needs: the multiplicity of a component of a closed
subscheme of a locally Noetherian scheme is automatically nonzero, by
`Stacks.Chow.componentMultiplicity_ne_zero`, so the specific value of the multiplicity — a
power of the characteristic in the inseparable case — plays no role here.

The reduced closure of a point is represented by the subscheme of its vanishing ideal sheaf and
its inverse image by the `comap` of that ideal sheaf, exactly as in the definition of the flat
pullback weight.

## References

* [Stacks Project, Section 0H4E](https://stacks.math.columbia.edu/tag/0H4E)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVH](https://stacks.math.columbia.edu/tag/0FVH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The underlying space of the reduced closure of a point is the closure of that point. -/
public theorem range_subschemeι_vanishingIdeal_closure {X : Scheme.{u}} (x : X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι.base =
      closure ({x} : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- In a flat base change of Chow situations, a point `x` of `X` of relative dimension `k` which
is the image of a point of `X ×_S S'` is the image of a point of `X ×_S S'` at which the weight
entering a base-changed cycle is nonzero.

The point is produced as the image of a generic point of the scheme-theoretic inverse image of
the reduced closure of `x`, whose relative dimension is `k + c` because that inverse image is
the base change of the reduced closure of `x`, a scheme of delta-dimension `k`. -/
private theorem exists_flatPullbackWeight_ne_zero_of_eq (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (x : X) (hx : relativeDimension B.base.dimensionFunction f x = k)
    (w : (pullback f B.g : Scheme.{u})) (hw : (pullback.fst f B.g).base w = x) :
    ∃ y : (pullback f B.g : Scheme.{u}), (pullback.fst f B.g).base y = x ∧
      flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g) (k + B.c) y
        ≠ 0 := by
  classical
  set q : (pullback f B.g : Scheme.{u}) ⟶ X := pullback.fst f B.g with hq
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  obtain ⟨ξ, -, hξ⟩ := exists_comap_genericPoint_over q x w hw
  refine ⟨(I.comap q).subschemeι.base ξ.1, hξ, ?_⟩
  set Z : Scheme.{u} := pullback (I.subschemeι ≫ f) B.g with hZ
  set e : (I.comap q).subscheme ≅ Z := I.comapIso q ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso f B.g I.subschemeι with he
  set j : Z ⟶ (pullback f B.g : Scheme.{u}) := e.inv ≫ (I.comap q).subschemeι with hj
  have : IsClosedImmersion j := by rw [hj]; infer_instance
  have hjsnd : j ≫ pullback.snd f B.g = pullback.snd (I.subschemeι ≫ f) B.g := by
    simp only [hj, he, Iso.trans_inv, Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, pullbackSymmetry_inv_comp_fst_assoc]
    exact pullbackRightPullbackFstIso_inv_snd_snd f B.g I.subschemeι
  have hdX : schemeDeltaDimension B.base (I.subschemeι ≫ f) = (k : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion,
      image_genericPoint_eq_of_range_eq_closure I.subschemeι x
        (range_subschemeι_vanishingIdeal_closure x), hx]
  set ζ : genericPoints Z := genericPointsIso e ξ with hζ
  have hdZ := deltaDimension_component_baseChange B (I.subschemeι ≫ f) k hdX
    (genericPoints.component ζ)
  rw [deltaDimension_eq_of_isGenericPoint _ _ _ ζ.1 (genericPoints.isGenericPoint ζ)] at hdZ
  have hjζ : j.base ζ.1 = (I.comap q).subschemeι.base ξ.1 := by
    have hinv : e.inv.base (e.hom.base ξ.1) = ξ.1 := by
      show ((e.hom ≫ e.inv) ξ.1) = ξ.1
      rw [Iso.hom_inv_id]
      rfl
    show (I.comap q).subschemeι.base (e.inv.base ζ.1) = _
    rw [show ζ.1 = e.hom.base ξ.1 from rfl, hinv]
  have hdim : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g)
      ((I.comap q).subschemeι.base ξ.1) = k + B.c := by
    rw [← hjζ, ← relativeDimension_comp_closedImmersion, hjsnd]
    exact hdZ
  exact flatPullbackWeight_ne_zero_of_genericPoint B.baseChange (pullback.snd f B.g) q (k + B.c)
    x ((I.comap q).subschemeι.base ξ.1) ξ rfl hξ hdim

/-- In a flat base change of Chow situations, a cycle on `X` whose base change to `X ×_S S'`
vanishes has coefficient zero at every point of `X` lying in the image of `X ×_S S'`. -/
theorem eq_zero_of_baseChangeCyclePullback_eq_zero_of_mem_range (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (z : CycleGroup B.base f k) (hz : baseChangeCyclePullback B f k z = 0) (x : X)
    (hx : x ∈ Set.range (pullback.fst f B.g).base) :
    z.1 x = 0 := by
  by_contra hne
  obtain ⟨w, hw⟩ := hx
  obtain ⟨y, hy, hweight⟩ := exists_flatPullbackWeight_ne_zero_of_eq B f k x
    ((mem_cyclesOfDimension_iff_forall_point B.base f k z.1).mp z.2 x hne) w hw
  have heval := congrArg (fun c ↦ c.1 y) hz
  rw [baseChangeCyclePullback_apply, hy] at heval
  exact mul_ne_zero hne hweight (by simpa using heval)

/-- In a flat base change of Chow situations whose base-change morphism is surjective on points,
the induced homomorphism `Z_k(X) ⟶ Z_{k+c}(X ×_S S')` on cycle groups is injective: a point
carrying a nonzero coefficient has above it a point of the base change at which the weight is
nonzero, so the base-changed cycle does not vanish there. -/
theorem injective_baseChangeCyclePullback_of_surjective (B : FlatBaseChangeSituation.{u})
    [Surjective B.g] {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ) :
    Function.Injective (baseChangeCyclePullback B f k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have : Surjective (pullback.fst f B.g) := inferInstance
  exact eq_zero_of_baseChangeCyclePullback_eq_zero_of_mem_range B f k z hz x
    ((pullback.fst f B.g).surjective x)

/-- **Stacks Project, Section 0H4E.** For a scheme `X` locally of finite type over a field `k`
and an arbitrary extension `K/k` of fields, the base-change homomorphism
`Z_r(X) ⟶ Z_r(X_K)` on cycle groups is injective. The extension is not assumed algebraic, nor
even of finite type. -/
@[stacks 0H4E "the base change map on cycle groups along a field extension, and its injectivity"]
theorem injective_baseChangeCyclePullback_fieldExtension (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (r : ℤ) :
    Function.Injective (baseChangeCyclePullback (fieldExtensionBaseChangeSituation k K) f r) :=
  injective_baseChangeCyclePullback_of_surjective (fieldExtensionBaseChangeSituation k K) f r

end Stacks.Chow

end
