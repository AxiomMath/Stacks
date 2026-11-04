module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback

/-!
# Axiom (A4) descends along a field extension

Let `Φ` be comparison data of Tag 0FVT between data `𝔇` for `(k, F)` and `𝔇'` for `(k', F')`.
If `(H')^*` satisfies axiom (A4), so does `H^*`. Let `i : Y → X` be the inclusion of an effective
Cartier divisor `D` and `a ∈ H^*(X)` with `i^*a = 0`. The projection `X_{k'} ⟶ X` is flat, so the
inverse image of `D` in `X_{k'}` is an effective Cartier divisor, whose closed subscheme is
`Y_{k'}`, and whose invertible sheaf is the pullback of `𝒪_X(D)`. The comparison of first twists
carries `a ∪ c₁^H(𝒪_X(D))` to `a_{k'} ∪ c₁^{H'}(𝒪_{X_{k'}}(D_{k'}))`, which vanishes by (A4) for
`(H')^*`; the comparison is injective, so `a ∪ c₁^H(𝒪_X(D)) = 0`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.baseChangeSubschemeIso`: `Y_{k'}` is the inverse
  image of `D` in `X_{k'}`.
* `Stacks.WeilCohomology.FieldExtensionComparison.twistOne_tateCupLeft`: the comparison of first
  twists is compatible with cup products by untwisted classes.
* `Stacks.WeilCohomology.FieldExtensionComparison.divisorAxiom`: axiom (A4) descends.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The morphism `Spec k' ⟶ Spec k` of a field extension is flat. -/
instance flat_specMap : Flat (ArtinSchreier.specExt k k') :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The projection `X_{k'} ⟶ X` is flat, as a base change of `Spec k' ⟶ Spec k`. -/
instance flat_baseChangeProj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Flat (baseChangeProj (k' := k') X) := by
  have : Flat (ArtinSchreier.specExt k k') := flat_specMap
  exact inferInstanceAs (Flat (pullback.fst X.obj.hom (ArtinSchreier.specExt k k')))

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} (i : Y ⟶ X)
  (D : ((toScheme k).obj X).IdealSheafData) (e : (toScheme k).obj Y ≅ D.subscheme)
  (he : e.hom ≫ D.subschemeι = (toScheme k).map i)

/-- `Y_{k'}` is the inverse image of `D` in `X_{k'}`, when `Y` is `D`. -/
def baseChangeSubschemeIso :
    (toScheme k').obj ((baseChange k k').obj Y) ≅
      (D.comap (baseChangeProj (k' := k') X)).subscheme :=
  have sq : IsPullback ((toScheme k').map ((baseChange k k').map i)) (baseChangeProj Y ≫ e.hom)
      (baseChangeProj X) D.subschemeι := by
    have h2 : IsPullback ((toScheme k).map i) e.hom (𝟙 _) D.subschemeι :=
      IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, he]⟩
    simpa using (isPullback_baseChange_map i).paste_vert h2
  sq.isoPullback ≪≫ (D.comapIso (baseChangeProj X)).symm

/-- The identification `Y_{k'} ≅ D_{k'}` is compatible with the closed immersions into `X_{k'}`. -/
theorem baseChangeSubschemeIso_hom_ι :
    (baseChangeSubschemeIso (k' := k') i D e he).hom ≫
        (D.comap (baseChangeProj (k' := k') X)).subschemeι =
      (toScheme k').map ((baseChange k k').map i) := by
  simp [baseChangeSubschemeIso]

end SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- The comparison of first twists sends `0` to `0`. -/
theorem twistOne_zero (X : (SmoothProjectiveScheme k).FullSubcategory) : Φ.twistOne X 0 = 0 := by
  simp [twistOne]

/-- The comparison of first twists is additive. -/
theorem twistOne_add (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x y : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    Φ.twistOne X (x + y) = Φ.twistOne X x + Φ.twistOne X y := by
  simp [twistOne, TensorProduct.tmul_add]

/-- The comparison of first twists is compatible with cup products by untwisted classes. -/
theorem twistOne_tateCupLeft (X : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X)
    (x : tateTwist F 𝔇.tate (𝔇.H X) 1) :
    Φ.twistOne X (tateCupLeft (L := 𝔇.tate) (𝔇.cup X) 1 a x) =
      tateCupLeft (L := 𝔇'.tate) (𝔇'.cup _) 1 (Φ.ρ X a) (Φ.twistOne X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [twistOne]
  | tmul v t =>
    simp only [twistOne, tateCupLeft, LinearMap.mk₂_apply, tateTwistMap, TensorProduct.map_tmul,
      LinearMap.id_coe, id_eq, FirstChernClassData.cup, LinearMap.mul_apply']
    rw [twistOneBaseChange_tmul, twistOneBaseChange_tmul, TensorProduct.map_tmul]
    simp only [AlgEquiv.toLinearMap_apply, LinearMap.mul_apply', LinearMap.id_coe, id_eq, ρ_apply,
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    rw [map_add, Φ.twistOne_add, Φ.twistOne_add, hx, hy, map_add]

include Φ in
/-- **Axiom (A4) descends**: if `(H')^*` satisfies axiom (A4), so does `H^*`. -/
theorem divisorAxiom (hA4' : 𝔇'.DivisorAxiom) : 𝔇.DivisorAxiom := by
  intro X Y i D hD e he a ha
  have := hD
  have hD' : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (baseChangeProj (k' := k') X)) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ D hD
  have : Stacks.Divisors.IsPullbackDefined (baseChangeProj (k' := k') X) D := hD'
  apply Φ.twistOne_injective X
  rw [Φ.twistOne_zero, Φ.twistOne_tateCupLeft]
  have hc : Φ.twistOne X (𝔇.c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.isInvertible_divisorSheaf D))) =
      𝔇'.c₁ _ (picardClassOf _ (Stacks.Divisors.divisorSheaf (D.comap (baseChangeProj X)))
        (Stacks.Divisors.isInvertible_divisorSheaf _)) :=
    (Φ.c₁_comm _ _ _).trans (congrArg _ (picardClassOf_eq_of_iso _ _ _ _ _
      (Stacks.Divisors.invertibleSheafPullbackIso (baseChangeProj X) D)))
  rw [hc]
  refine hA4' _ _ ((baseChange k k').map i) _ hD' (baseChangeSubschemeIso i D e he)
    (baseChangeSubschemeIso_hom_ι i D e he) (Φ.ρ X a) ?_
  rw [ρ_apply, ← Φ.iso_natural, ha, TensorProduct.tmul_zero, map_zero]

end FieldExtensionComparison

end Stacks.WeilCohomology
