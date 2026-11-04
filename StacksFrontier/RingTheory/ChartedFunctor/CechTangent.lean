module

public import StacksFrontier.RingTheory.ChartedFunctor.BaseSection
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The Čech complex of the tangent along a faithfully flat cover is exact in degree one

Let `F` be a functor on bounded `R`-algebras with an étale chart, `I` an ideal of `R` of square
zero, `x` a section of `F` over `R ⧸ I`, and `R → S` faithfully flat, such that `x` has a chart
point over `S ⧸ I S`. Write `S⁽ⁿ⁾` for the `n + 1`-fold tensor power of `S` over `R`, nested to
the left, and `T⁽ⁿ⁾` for the tangent of `F` at the pull-back of `x` to `S⁽ⁿ⁾ ⧸ I S⁽ⁿ⁾`. The
coface maps of the Čech nerve induce maps of tangents, and the Čech complex
```
T⁽⁰⁾ ⟶ T⁽¹⁾ ⟶ T⁽²⁾
```
is exact at `T⁽¹⁾`.

The argument is the standard one. By faithful flatness it suffices to check exactness after
`- ⊗_R S`. The tangent is quasi-coherent — `T⁽ⁿ⁾ ⊗_R S ≅ T⁽ⁿ⁺¹⁾` along the inclusion of the
first `n + 1` factors, by `Stacks.ChartedFunctor.Tan.bijective_linMap` and the flat base change of
the conormal module — and under these isomorphisms the base-changed complex is the Čech complex
with its last coface maps omitted, which the last codegeneracy contracts.

## Main results

* `Stacks.ChartedFunctor.Cech.exact`: exactness of the Čech complex of the tangent at `T⁽¹⁾`.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal TensorProduct

universe u

namespace Stacks.ChartedFunctor

namespace Cech

open BaseSection

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]

/-! ### The Čech nerve in low degrees -/

section Nerve

variable (S : BoundedAlg R κ)

/-- `S⁽¹⁾ = S ⊗ S`. -/
abbrev L1 : BoundedAlg R κ := tens S S
/-- `S⁽²⁾ = (S ⊗ S) ⊗ S`. -/
abbrev L2 : BoundedAlg R κ := tens (L1 S) S
/-- `S⁽³⁾ = ((S ⊗ S) ⊗ S) ⊗ S`. -/
abbrev L3 : BoundedAlg R κ := tens (L2 S) S

/-- The coface `S ⟶ S⁽¹⁾`, `s ↦ 1 ⊗ s`. -/
abbrev δ00 : S ⟶ L1 S := inclR S S
/-- The coface `S ⟶ S⁽¹⁾`, `s ↦ s ⊗ 1`. -/
abbrev δ01 : S ⟶ L1 S := inclL S S
/-- The coface `S⁽¹⁾ ⟶ S⁽²⁾`, `y ⊗ c ↦ δ₀₀ y ⊗ c`. -/
abbrev δ10 : L1 S ⟶ L2 S := tensMap (δ00 S) S
/-- The coface `S⁽¹⁾ ⟶ S⁽²⁾`, `y ⊗ c ↦ δ₀₁ y ⊗ c`. -/
abbrev δ11 : L1 S ⟶ L2 S := tensMap (δ01 S) S
/-- The coface `S⁽¹⁾ ⟶ S⁽²⁾`, `y ↦ y ⊗ 1`. -/
abbrev δ12 : L1 S ⟶ L2 S := inclL (L1 S) S
/-- The coface `S⁽²⁾ ⟶ S⁽³⁾`, `y ⊗ d ↦ δ₁₀ y ⊗ d`. -/
abbrev δ20 : L2 S ⟶ L3 S := tensMap (δ10 S) S
/-- The coface `S⁽²⁾ ⟶ S⁽³⁾`, `y ⊗ d ↦ δ₁₁ y ⊗ d`. -/
abbrev δ21 : L2 S ⟶ L3 S := tensMap (δ11 S) S
/-- The coface `S⁽²⁾ ⟶ S⁽³⁾`, `y ⊗ d ↦ δ₁₂ y ⊗ d`. -/
abbrev δ22 : L2 S ⟶ L3 S := tensMap (δ12 S) S
/-- The coface `S⁽²⁾ ⟶ S⁽³⁾`, `y ↦ y ⊗ 1`. -/
abbrev δ23 : L2 S ⟶ L3 S := inclL (L2 S) S

/-- The last codegeneracy `S⁽²⁾ ⟶ S⁽¹⁾`, `y ⊗ c ↦ y · (1 ⊗ c)`. -/
abbrev σ2 : L2 S ⟶ L1 S :=
  BoundedAlg.ofHom (Algebra.TensorProduct.lift (AlgHom.id R (L1 S).obj)
    (BoundedAlg.toAlgHom (inclR S S)) fun _ _ => Commute.all _ _)

/-- The last codegeneracy `S⁽³⁾ ⟶ S⁽²⁾`, `y ⊗ d ↦ y · (1 ⊗ d)`. -/
abbrev σ3 : L3 S ⟶ L2 S :=
  BoundedAlg.ofHom (Algebra.TensorProduct.lift (AlgHom.id R (L2 S).obj)
    (BoundedAlg.toAlgHom (inclR (L1 S) S)) fun _ _ => Commute.all _ _)

/-- Equality of algebra maps out of an iterated tensor product, on pure tensors. -/
macro "tens_ext" : tactic =>
  `(tactic| (apply BoundedAlg.hom_ext; (repeat' apply Algebra.TensorProduct.ext) <;>
    (apply AlgHom.ext; intro; rfl)))

/-- The cosimplicial identity `δ₁₀ ∘ δ₀₀ = δ₁₁ ∘ δ₀₀`. -/
lemma δ10_δ00 : δ00 S ≫ δ10 S = δ00 S ≫ δ11 S := by tens_ext
/-- The cosimplicial identity `δ₁₀ ∘ δ₀₁ = δ₁₂ ∘ δ₀₀`. -/
lemma δ10_δ01 : δ01 S ≫ δ10 S = δ00 S ≫ δ12 S := by tens_ext
/-- The cosimplicial identity `δ₁₁ ∘ δ₀₁ = δ₁₂ ∘ δ₀₁`. -/
lemma δ11_δ01 : δ01 S ≫ δ11 S = δ01 S ≫ δ12 S := by tens_ext
/-- The cosimplicial identity `δ₂₀ ∘ δ₁₀ = δ₂₁ ∘ δ₁₀`. -/
lemma δ20_δ10 : δ10 S ≫ δ20 S = δ10 S ≫ δ21 S := by tens_ext
/-- The cosimplicial identity `δ₂₀ ∘ δ₁₁ = δ₂₂ ∘ δ₁₀`. -/
lemma δ20_δ11 : δ11 S ≫ δ20 S = δ10 S ≫ δ22 S := by tens_ext
/-- The cosimplicial identity `δ₂₁ ∘ δ₁₁ = δ₂₂ ∘ δ₁₁`. -/
lemma δ21_δ11 : δ11 S ≫ δ21 S = δ11 S ≫ δ22 S := by tens_ext
/-- Equality of algebra maps out of an iterated tensor product, on pure tensors, after
evaluating `Algebra.TensorProduct.lift`. -/
macro "tens_ext_simp" : tactic =>
  `(tactic| (apply BoundedAlg.hom_ext; (repeat' apply Algebra.TensorProduct.ext) <;>
    (apply AlgHom.ext; intro; simp [Algebra.TensorProduct.lift_tmul] <;> rfl)))

/-- The codegeneracy `σ₃` is a retraction of the coface `δ₂₂`. -/
lemma σ3_δ22 : δ22 S ≫ σ3 S = 𝟙 _ := by tens_ext_simp
/-- The cosimplicial identity `σ₃ ∘ δ₂₀ = δ₁₀ ∘ σ₂`. -/
lemma σ3_δ20 : δ20 S ≫ σ3 S = σ2 S ≫ δ10 S := by tens_ext_simp
/-- The cosimplicial identity `σ₃ ∘ δ₂₁ = δ₁₁ ∘ σ₂`. -/
lemma σ3_δ21 : δ21 S ≫ σ3 S = σ2 S ≫ δ11 S := by tens_ext_simp

end Nerve

/-! ### The Čech complex of the tangent -/

section Tangent

variable {F : BoundedAlg R κ ⥤ Type u} (hR : #R < κ) (I : Ideal R)
  (x : F.obj (quot (base hR) I))

/-- The tangent of `F` at the pull-back of `x` to `P ⧸ I P`. -/
def T (P : BoundedAlg R κ) : Type u := Tan F P (ideal I P) (pt hR I x P)

variable {hR I x}

/-- The additive group structure on the tangent `T P`. -/
instance instAddCommGroupT (P : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x P))] :
    AddCommGroup (T hR I x P) :=
  Tan.instAddCommGroup

/-- The `R`-module structure on the tangent `T P`. -/
instance instModuleT (P : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x P))] :
    Module R (T hR I x P) :=
  Tan.instModuleBase

/-- Scalar multiplication of tangent vectors by elements of `P ⧸ I P`. -/
def smulT (P : BoundedAlg R κ) (a : P.obj ⧸ ideal I P) (w : T hR I x P) : T hR I x P :=
  @HSMul.hSMul _ (Tan F P (ideal I P) (pt hR I x P)) _ instHSMul a w

/-- Scalar multiplication of tangent vectors distributes over subtraction. -/
lemma smulT_sub (P : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x P))]
    (a : P.obj ⧸ ideal I P) (w w' : T hR I x P) :
    smulT P a (w - w') = smulT P a w - smulT P a w' :=
  smul_sub (A := Tan F P (ideal I P) (pt hR I x P)) a w w'

/-- Scalar multiplication of tangent vectors distributes over addition. -/
lemma smulT_add (P : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x P))]
    (a : P.obj ⧸ ideal I P) (w w' : T hR I x P) :
    smulT P a (w + w') = smulT P a w + smulT P a w' :=
  smul_add (A := Tan F P (ideal I P) (pt hR I x P)) a w w'

/-- The map of tangents along an algebra map. -/
abbrev dT {P Q : BoundedAlg R κ} (f : P ⟶ Q) [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x Q))] : T hR I x P →ₗ[R] T hR I x Q :=
  Tan.mapₗ f (ideal_le_comap I f) (pt_map f)

/-- The map of tangents along a composite is the composite of the maps of tangents. -/
lemma dT_comp {P Q W : BoundedAlg R κ} (f : P ⟶ Q) (g : Q ⟶ W)
    [Fact (HasChartPoint F (pt hR I x P))] [Fact (HasChartPoint F (pt hR I x Q))]
    [Fact (HasChartPoint F (pt hR I x W))] (w : T hR I x P) :
    dT g (dT f w) = dT (f ≫ g) w :=
  Tan.map_map f (ideal_le_comap I f) (pt_map f) g (ideal_le_comap I g) (pt_map g) w

/-- The map of tangents along the identity is the identity. -/
lemma dT_id {P : BoundedAlg R κ} [Fact (HasChartPoint F (pt hR I x P))] (w : T hR I x P) :
    dT (𝟙 P) w = w :=
  Tan.map_id (pt_map (𝟙 P)) w

/-- Equal algebra maps induce equal maps of tangents. -/
lemma dT_eq {P Q : BoundedAlg R κ} {f g : P ⟶ Q} (h : f = g)
    [Fact (HasChartPoint F (pt hR I x P))] [Fact (HasChartPoint F (pt hR I x Q))]
    (w : T hR I x P) : dT f w = dT g w := by
  subst h
  rfl

variable (S : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x S))]

/-- `x` has a chart point over `S⁽¹⁾ ⧸ I S⁽¹⁾`, pulled back along `δ₀₁`. -/
instance instFactL1 : Fact (HasChartPoint F (pt hR I x (L1 S))) :=
  ⟨hasChartPoint_pt (δ01 S) Fact.out⟩

/-- `x` has a chart point over `S⁽²⁾ ⧸ I S⁽²⁾`, pulled back along `δ₁₂`. -/
instance instFactL2 : Fact (HasChartPoint F (pt hR I x (L2 S))) :=
  ⟨hasChartPoint_pt (δ12 S) Fact.out⟩

/-- `x` has a chart point over `S⁽³⁾ ⧸ I S⁽³⁾`, pulled back along `δ₂₃`. -/
instance instFactL3 : Fact (HasChartPoint F (pt hR I x (L3 S))) :=
  ⟨hasChartPoint_pt (δ23 S) Fact.out⟩

/-- The differential `T⁽⁰⁾ ⟶ T⁽¹⁾`. -/
abbrev d0 : T hR I x S →ₗ[R] T hR I x (L1 S) := dT (δ00 S) - dT (δ01 S)

/-- The differential `T⁽¹⁾ ⟶ T⁽²⁾`. -/
abbrev d1 : T hR I x (L1 S) →ₗ[R] T hR I x (L2 S) := dT (δ10 S) - dT (δ11 S) + dT (δ12 S)

/-- The base-changed differential `T⁽¹⁾ ⟶ T⁽²⁾`, the last coface omitted. -/
abbrev d0' : T hR I x (L1 S) →ₗ[R] T hR I x (L2 S) := dT (δ10 S) - dT (δ11 S)

/-- The base-changed differential `T⁽²⁾ ⟶ T⁽³⁾`, the last coface omitted. -/
abbrev d1' : T hR I x (L2 S) →ₗ[R] T hR I x (L3 S) :=
  dT (δ20 S) - dT (δ21 S) + dT (δ22 S)

/-- Composites of maps of tangents along equal composites of algebra maps agree. -/
private lemma dT_comp_congr {P Q Q' W : BoundedAlg R κ} {f : P ⟶ Q} {g : Q ⟶ W} {f' : P ⟶ Q'}
    {g' : Q' ⟶ W} (h : f ≫ g = f' ≫ g') [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x Q))] [Fact (HasChartPoint F (pt hR I x Q'))]
    [Fact (HasChartPoint F (pt hR I x W))] (w : T hR I x P) :
    dT g (dT f w) = dT g' (dT f' w) := by
  rw [dT_comp, dT_comp, dT_eq h]

/-- **The base-changed complex is exact**, contracted by the last codegeneracy. -/
lemma exact_d0'_d1' : Function.Exact (d0' (F := F) (hR := hR) (I := I) (x := x) S) (d1' S) := by
  refine fun y => ⟨fun hy => ⟨-dT (σ2 S) y, ?_⟩, ?_⟩
  · have h := congrArg (dT (σ3 S)) hy
    simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, map_zero] at h
    rw [dT_comp_congr (σ3_δ20 S), dT_comp_congr (σ3_δ21 S), dT_comp (δ22 S) (σ3 S),
      dT_eq (σ3_δ22 S), dT_id] at h
    simp only [LinearMap.sub_apply, map_neg]
    rw [← sub_eq_zero, ← neg_eq_zero, ← h]
    abel
  · rintro ⟨w, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.sub_apply, map_sub]
    rw [dT_comp_congr (δ20_δ10 S), dT_comp_congr (δ20_δ11 S), dT_comp_congr (δ21_δ11 S)]
    abel

/-! ### Base change and faithful flatness -/

variable (hI : I ^ 2 = ⊥) [Module.Flat R S.obj]

omit [Fact (HasChartPoint F (pt hR I x S))] [Module.Flat R S.obj] in
/-- The linearised map of tangents along the inclusion `P ⟶ P ⊗_R S`. -/
def bcMap (P : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x (tens P S)))] :
    T hR I x P ⊗[R] S.obj →ₗ[R] T hR I x (tens P S) :=
  Tan.linMap (inclL P S) (ideal_le_comap I (inclL P S)) (pt_map (inclL P S)) S.obj
      (BoundedAlg.toAlgHom (inclR P S))

omit [Fact (HasChartPoint F (pt hR I x S))] in
/-- **Quasi-coherence of the tangent**: `T(P) ⊗_R S ≅ T(P ⊗_R S)` along the inclusion of `P`. -/
def bc (hI : I ^ 2 = ⊥) (P : BoundedAlg R κ) [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x (tens P S)))] :
    T hR I x P ⊗[R] S.obj ≃ₗ[R] T hR I x (tens P S) :=
  LinearEquiv.ofBijective (bcMap S P)
    (Tan.bijective_linMap _ _ _ _ _ (bijective_conormalLinMap_tens I hI P S))

omit [Fact (HasChartPoint F (pt hR I x S))] [Module.Flat R S.obj] in
/-- The base change isomorphism sends `w ⊗ s` to `(1 ⊗ s) • dT (inclL P S) w`. -/
lemma bc_tmul (P : BoundedAlg R κ) [Module.Flat R S.obj] [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x (tens P S)))] (w : T hR I x P) (s : S.obj) :
    bc S hI P (w ⊗ₜ s) =
      smulT (tens P S) (Ideal.Quotient.mkₐ R (ideal I (tens P S)) ((1 : P.obj) ⊗ₜ[R] s))
        (dT (inclL P S) w) :=
  rfl

/-- Maps of tangents along a coface commute with scalars from the last factor. -/
lemma dT_smul {P Q : BoundedAlg R κ} (f : P ⟶ Q) [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x Q))] (a : P.obj) (w : T hR I x P) :
    dT f (smulT P (Ideal.Quotient.mkₐ R (ideal I P) a) w) =
      smulT Q (Ideal.Quotient.mkₐ R (ideal I Q) (BoundedAlg.toAlgHom f a)) (dT f w) :=
  Tan.map_smul f (ideal_le_comap I f) (pt_map f) _ w

omit [Fact (HasChartPoint F (pt hR I x S))] [Module.Flat R S.obj] in
/-- The map `f ⊗ S` sends `1 ⊗ s` to `1 ⊗ s`. -/
lemma tensMap_one_tmul {P Q : BoundedAlg R κ} (f : P ⟶ Q) (s : S.obj) :
    BoundedAlg.toAlgHom (tensMap f S) ((1 : P.obj) ⊗ₜ[R] s) = (1 : Q.obj) ⊗ₜ[R] s := by
  change Algebra.TensorProduct.map _ _ (1 ⊗ₜ s) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

omit [Fact (HasChartPoint F (pt hR I x S))] in
/-- The base change isomorphisms commute with the maps of tangents along `f` and `f ⊗ S`. -/
lemma bc_natural {P Q : BoundedAlg R κ} (f : P ⟶ Q) [Fact (HasChartPoint F (pt hR I x P))]
    [Fact (HasChartPoint F (pt hR I x Q))] [Fact (HasChartPoint F (pt hR I x (tens P S)))]
    [Fact (HasChartPoint F (pt hR I x (tens Q S)))] (w : T hR I x P) (s : S.obj) :
    dT (tensMap f S) (bc S hI P (w ⊗ₜ s)) = bc S hI Q (dT f w ⊗ₜ s) := by
  rw [bc_tmul, bc_tmul, dT_smul, tensMap_one_tmul, dT_comp, dT_comp,
    dT_eq (inclL_tensMap f S)]

/-- The base change isomorphisms intertwine `d0 ⊗ S` with `d0'`. -/
lemma sq1 : d0' S ∘ₗ (bc S hI S).toLinearMap =
    (bc S hI (L1 S)).toLinearMap ∘ₗ
      LinearMap.rTensor S.obj (d0 (hR := hR) (I := I) (x := x) S) := by
  apply TensorProduct.ext'
  intro w s
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, LinearMap.sub_apply, sub_tmul, map_sub, bc_natural]

/-- The base change isomorphisms intertwine `d1 ⊗ S` with `d1'`. -/
lemma sq2 : d1' S ∘ₗ (bc S hI (L1 S)).toLinearMap =
    (bc S hI (L2 S)).toLinearMap ∘ₗ
      LinearMap.rTensor S.obj (d1 (hR := hR) (I := I) (x := x) S) := by
  apply TensorProduct.ext'
  intro w s
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, LinearMap.sub_apply, LinearMap.add_apply, sub_tmul, add_tmul,
    map_sub, map_add, bc_natural]

omit [Module.Flat R S.obj] in
/-- **The Čech complex of the tangent is exact in degree one**, along a faithfully flat
`R → S` through which `x` has a chart point. -/
theorem exact (hI : I ^ 2 = ⊥) [Module.FaithfullyFlat R S.obj] :
    Function.Exact (d0 (hR := hR) (I := I) (x := x) S) (d1 S) := by
  rw [← Module.FaithfullyFlat.rTensor_exact_iff_exact R S.obj]
  exact (Function.Exact.iff_of_ladder_linearEquiv (sq1 S hI) (sq2 S hI)).1 (exact_d0'_d1' S)

end Tangent

end Cech

end Stacks.ChartedFunctor

end
