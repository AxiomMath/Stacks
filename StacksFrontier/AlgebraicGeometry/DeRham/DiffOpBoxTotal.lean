module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.Interval
public import StacksCore.Algebra.Homology.Bifunctor
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpComplex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts

/-!
# The total complex of the box product of two relative de Rham complexes

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. The box product of [Stacks, Tag 0G46]
is a bifunctor between categories of finite-order differential operators, bilinear on morphisms,
so the construction of [Stacks, Tag 0A5J] turns the two relative de Rham complexes `Ω^•_{X/S}`
and `Ω^•_{Y/S}` into a double complex `Ω^p_{X/S} ⊠ Ω^q_{Y/S}` of finite-order differential
operators on `X ×_S Y / S`, and the total complex of [Stacks, Tag 012Z] turns that into a single
complex

`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`,

the left-hand side of the de Rham Künneth formula.

## Main definitions

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductCurried`: the box-product
  bifunctor in curried form.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxDoubleComplex`: **the double complex
  `Ω^p_{X/S} ⊠ Ω^q_{Y/S}`.**
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotal`: **the total complex
  `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`.**

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_zero_left` and
  `boxHom_zero_right`: the box product of a zero operator with anything is zero, so the curried
  bifunctor preserves zero morphisms in each variable.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hasMapBifunctor`: **the total complex
  of the box-product bicomplex of two `ℕ`-indexed cochain complexes exists.** The category of
  finite-order differential operators has finite biproducts and, in each total degree `n`, only
  the finitely many pairs `(p, q)` with `p + q = n` contribute.
* `HomologicalComplex.hasMapBifunctor_up_ℤ_of_isZero`: **the total complex of the bicomplex
  `F(K^p, L^q)` of two `ℤ`-indexed cochain complexes which vanish in degrees `< n₁` and `< n₂`
  exists**, for any bifunctor `F` additive in each variable into a category with finite
  coproducts.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hasMapBifunctor_up_ℤ`: **the total
  complex of the box-product bicomplex of two `ℤ`-indexed cochain complexes which are strictly
  `≥ n₁` and strictly `≥ n₂` exists.** Boundedness below is a genuine hypothesis here; see the
  implementation notes.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.ιMapBifunctor_d_up_ℤ`: the
  differential of that total complex on the summand of degree `(p, q)` is
  `d_K ⊠ 1 + (-1)^p (1 ⊠ d_L)`.
* `AlgebraicGeometry.Scheme.Hom.deRhamBoxDoubleComplex_X_X`,
  `AlgebraicGeometry.Scheme.Hom.deRhamBoxDoubleComplex_d_f` and
  `AlgebraicGeometry.Scheme.Hom.deRhamBoxDoubleComplex_X_d`: the term of the double complex in
  degree `(p, q)` is `Ω^p_{X/S} ⊠ Ω^q_{Y/S}`, and its two differentials are the de Rham
  differentials boxed with the identities.
* `HomologicalComplex₂.ιTotal_d_up_ℕ`: the differential of the total complex of a bicomplex of
  `ℕ`-indexed cochain complexes is `d₁ + (-1)^p d₂` on the summand of degree `(p, q)`, which is
  the sign convention of [Stacks, Tag 012Z].
* `ComplexShape.ε_up_ℤ_natCast`: the `ℕ`-indexed and `ℤ`-indexed sign conventions agree in
  nonnegative degrees.

## Implementation notes

The signs are the ones of [Stacks, Tag 012Z]: the `ComplexShape.TotalComplexShape` deduced from
`ComplexShape.TensorSigns (ComplexShape.up ℕ)` has `π (p, q) = p + q`, `ε₁ = 1` and
`ε₂ (p, q) = (-1)^p`, so the differential on the summand `Ω^p ⊠ Ω^q` is `d₁ + (-1)^p d₂`;
`HomologicalComplex₂.ιTotal_d_up_ℕ` states that. That `TensorSigns` instance is the one of
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic`. For `ℤ` the signs are Mathlib's instance
`ComplexShape.TensorSigns (ComplexShape.up ℤ)`, whose `ε n = n.negOnePow` is the same convention:
`ComplexShape.ε_up_ℤ_natCast` is the agreement of the two in the degrees where both are defined.

The existence of the total complex is `HomologicalComplex₂.hasTotal_of_finite` rather than the
countable-coproducts criterion: the category of finite-order differential operators is only known
to have *finite* biproducts, since the quasi-coherence of an infinite direct sum of quasi-coherent
modules is not available (and is false in general, [Stacks, Tag 01CL]). The finiteness hypothesis
is satisfied for a reason independent of the complexes: the antidiagonal of `n` in `ℕ × ℕ` is
finite.

For `ℤ`-indexed complexes that reason disappears, the antidiagonal of `n` in `ℤ × ℤ` being
infinite, and the finiteness has to come from the complexes instead: if `K^p = 0` for `p < n₁`
and `L^q = 0` for `q < n₂`, then a pair with `p + q = n` and `K^p ⊠ L^q` nonzero has
`n₁ ≤ p ≤ n - n₂`. Some such hypothesis is necessary, not merely convenient: for unbounded
complexes the term of total degree `n` is a coproduct of infinitely many nonzero objects, and a
morphism out of an infinite direct sum of quasi-coherent modules whose components are operators
of unbounded order is of no finite order, so that coproduct does not exist in the category.

## References

* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
* [Stacks Project, Tag 0A5J](https://stacks.math.columbia.edu/tag/0A5J)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- The vertical sign of the total complex of a bicomplex of `ℕ`-indexed cochain complexes in
degree `p` is `(-1)^p`, the sign of [Stacks, Tag 012Z]. -/
theorem ComplexShape.ε_up_ℕ (p : ℕ) : (ComplexShape.up ℕ).ε p = (-1 : ℤˣ) ^ p := rfl

/-- The `ℕ`-indexed and `ℤ`-indexed sign conventions of [Stacks, Tag 012Z] agree where they
overlap: in a nonnegative degree the vertical sign is `(-1)^p` whether the degree is read in `ℕ`
or in `ℤ`. -/
theorem ComplexShape.ε_up_ℤ_natCast (p : ℕ) :
    (ComplexShape.up ℤ).ε (p : ℤ) = (ComplexShape.up ℕ).ε p := by
  rw [ComplexShape.ε_up_ℤ, Int.negOnePow_def, zpow_natCast, ComplexShape.ε_up_ℕ]

/-- **[Stacks, Tag 012Z], the differential summand-wise for a bicomplex of `ℕ`-indexed cochain
complexes**: on the summand `A^{p, q}` of `Tot(A)^n` it is `d₁^{p, q} + (-1)^p d₂^{p, q}`. -/
theorem HomologicalComplex₂.ιTotal_d_up_ℕ {C : Type*} [Category C] [Preadditive C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    [K.HasTotal (ComplexShape.up ℕ)] (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) =
      (K.d p (p + 1)).f q ≫
          K.ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) (by dsimp; omega) +
        ((-1 : ℤˣ) ^ p) • ((K.X p).d q (q + 1) ≫
          K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (by dsimp; omega)) := by
  rw [K.total_d, Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq (ComplexShape.up ℕ) (i₁ := p) (i₁' := p + 1) rfl q (n + 1) (by dsimp; omega),
    K.d₂_eq (ComplexShape.up ℕ) p (i₂ := q) (i₂' := q + 1) rfl (n + 1) (by dsimp; omega)]
  simp [ComplexShape.ε_up_ℕ]

/-- **The total complex of the bicomplex `F(K^p, L^q)` of two bounded-below `ℤ`-indexed cochain
complexes exists**, for a bifunctor `F` additive in each variable into a category with finite
coproducts: a pair with `p + q = n` and `F(K^p, L^q)` nonzero has `n₁ ≤ p ≤ n - n₂`, so only
finitely many pairs contribute in each total degree. -/
theorem HomologicalComplex.hasMapBifunctor_up_ℤ_of_isZero {C₁ C₂ D : Type*} [Category* C₁]
    [Category* C₂] [Category* D] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    [HasFiniteCoproducts D] (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    (n₁ n₂ : ℤ) (hK : ∀ p, p < n₁ → IsZero (K.X p)) (hL : ∀ q, q < n₂ → IsZero (L.X q)) :
    HasMapBifunctor K L F (ComplexShape.up ℤ) := by
  have key : ∀ p q : ℤ, IsZero (K.X p) → IsZero ((F.obj (K.X p)).obj (L.X q)) := by
    intro p q h
    rw [IsZero.iff_id_eq_zero, ← NatTrans.id_app, ← F.map_id,
      (IsZero.iff_id_eq_zero (K.X p)).1 h, F.map_zero]
    rfl
  refine HomologicalComplex₂.hasTotal_of_finite _ _ fun n => ?_
  refine Set.Finite.subset ((Set.finite_Icc n₁ (n - n₂)).image fun p => (p, n - p)) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have hp : n₁ ≤ p := le_of_not_gt fun hp ↦ hz (key p q (hK p hp))
  have hq : n₂ ≤ q := le_of_not_gt fun hq ↦ hz (Functor.map_isZero (F.obj (K.X p)) (hL q hq))
  exact ⟨p, ⟨hp, by lia⟩, by simp [show n - p = q by lia]⟩

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **The box product of a zero operator on `X/S` with an operator on `Y/S` is zero**, by
additivity of the box product in its first argument. -/
theorem boxHom_zero_left {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (E : G ⟶ G') :
    boxHom (0 : F ⟶ F') E = 0 := by
  refine (left_eq_add (a := boxHom (0 : F ⟶ F') E)).1 ?_
  rw [← boxHom_add_left, add_zero]

/-- **The box product of an operator on `X/S` with a zero operator on `Y/S` is zero**, by
additivity of the box product in its second argument. -/
theorem boxHom_zero_right {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') :
    boxHom D (0 : G ⟶ G') = 0 := by
  refine (left_eq_add (a := boxHom D (0 : G ⟶ G'))).1 ?_
  rw [← boxHom_add_right, add_zero]

/-- The box-product bifunctor of [Stacks, Tag 0G46] in curried form: the functor sending a
quasi-coherent module `F` on `X` to the functor `G ↦ F ⊠ G`. -/
noncomputable abbrev boxProductCurried (a : X ⟶ S) (b : Y ⟶ S) :
    FiniteOrderDifferentialOperatorCategory a ⥤
      FiniteOrderDifferentialOperatorCategory b ⥤
        FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a) :=
  Functor.curryObj (boxProductFunctor a b)

/-- Boxing with a fixed module on `X` preserves zero morphisms. -/
instance boxProductCurried_obj_preservesZeroMorphisms
    (F : FiniteOrderDifferentialOperatorCategory a) :
    ((boxProductCurried a b).obj F).PreservesZeroMorphisms where
  map_zero _ _ := boxHom_zero_right (𝟙 F)

/-- The curried box product preserves zero morphisms. -/
instance boxProductCurried_preservesZeroMorphisms :
    (boxProductCurried a b).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext G
    exact boxHom_zero_left (𝟙 G)

/-- For each `n` there are only finitely many pairs of natural numbers summing to `n`. -/
theorem finite_setOf_add_eq (n : ℕ) : {pq : ℕ × ℕ | pq.1 + pq.2 = n}.Finite :=
  Set.Finite.ofFinset (Finset.antidiagonal n) (fun _ => Finset.mem_antidiagonal)

/-- **The total complex of the box-product bicomplex of two `ℕ`-indexed cochain complexes of
finite-order differential operators exists.** The category has finite biproducts, and in each
total degree only the pairs `(p, q)` with `p + q = n` contribute, of which there are finitely
many. -/
instance hasMapBifunctor
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℕ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℕ) :
    HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _
    (fun n => Set.Finite.subset (finite_setOf_add_eq n) (fun _ h => h.1))

/-- **The total complex of the box-product bicomplex of two bounded-below `ℤ`-indexed cochain
complexes of finite-order differential operators exists.** In total degree `n` only the pairs
`(p, q)` with `p + q = n`, `n₁ ≤ p` and `n₂ ≤ q` contribute, of which there are finitely many,
and the category has finite biproducts. -/
theorem hasMapBifunctor_up_ℤ
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) (n₁ n₂ : ℤ)
    [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] :
    HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ) :=
  HomologicalComplex.hasMapBifunctor_up_ℤ_of_isZero K L _ n₁ n₂
    (fun p hp => K.isZero_of_isStrictlyGE n₁ p hp)
    (fun q hq => L.isZero_of_isStrictlyGE n₂ q hq)

/-- **[Stacks, Tag 012Z] for the box product of two `ℤ`-indexed cochain complexes**: on the
summand `K^p ⊠ L^q` of `Tot(K ⊠ L)^n` the differential is `d_K ⊠ 1 + (-1)^p (1 ⊠ d_L)`. -/
theorem ιMapBifunctor_d_up_ℤ
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    [HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)]
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ) p q n h ≫
        (HomologicalComplex.mapBifunctor K L (boxProductCurried a b)
          (ComplexShape.up ℤ)).d n (n + 1) =
      boxHom (K.d p (p + 1)) (𝟙 (L.X q)) ≫
          HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)
            (p + 1) q (n + 1) (by dsimp; lia) +
        p.negOnePow • (boxHom (𝟙 (K.X p)) (L.d q (q + 1)) ≫
          HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)
            p (q + 1) (n + 1) (by dsimp; lia)) := by
  refine (HomologicalComplex₂.ιTotal_d_up_ℤ _ p q n h).trans ?_
  have h₁ : (((((boxProductCurried a b).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).d p (p + 1)).f q =
      boxHom (K.d p (p + 1)) (𝟙 (L.X q)) :=
    Functor.mapBifunctorHomologicalComplex_obj_obj_d_f _ _ _ K L p (p + 1) q
  have h₂ : (((((boxProductCurried a b).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L).X p).d q (q + 1) =
      boxHom (𝟙 (K.X p)) (L.d q (q + 1)) :=
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d _ _ _ K L p q (q + 1)
  rw [h₁, h₂]
  rfl

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

namespace AlgebraicGeometry.Scheme.Hom

open FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The double complex `Ω^p_{X/S} ⊠ Ω^q_{Y/S}` of finite-order differential operators on
`X ×_S Y / S`**, obtained from the two relative de Rham complexes by the construction of
[Stacks, Tag 0A5J] applied to the box-product bifunctor. -/
noncomputable abbrev deRhamBoxDoubleComplex :
    HomologicalComplex₂ (FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (((boxProductCurried a b).mapBifunctorHomologicalComplex
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj (deRhamDiffOpComplex a)).obj
    (deRhamDiffOpComplex b)

/-- The term of the double complex in degree `(p, q)` is `Ω^p_{X/S} ⊠ Ω^q_{Y/S}`. -/
@[simp] theorem deRhamBoxDoubleComplex_X_X (p q : ℕ) :
    ((deRhamBoxDoubleComplex a b).X p).X q =
      boxProductObj (deRhamDiffOpTerm a p) (deRhamDiffOpTerm b q) :=
  rfl

/-- The first differential of the double complex is the de Rham differential of `X/S` boxed with
the identity of `Ω^q_{Y/S}`. -/
theorem deRhamBoxDoubleComplex_d_f (p q : ℕ) :
    ((deRhamBoxDoubleComplex a b).d p (p + 1)).f q =
      boxHom (deRhamDiffOpDifferential a p) (𝟙 (deRhamDiffOpTerm b q)) := by
  simp [Functor.curryObj, boxProductFunctor]

/-- The second differential of the double complex is the identity of `Ω^p_{X/S}` boxed with the
de Rham differential of `Y/S`. -/
theorem deRhamBoxDoubleComplex_X_d (p q : ℕ) :
    ((deRhamBoxDoubleComplex a b).X p).d q (q + 1) =
      boxHom (𝟙 (deRhamDiffOpTerm a p)) (deRhamDiffOpDifferential b q) := by
  simp [Functor.curryObj, boxProductFunctor]

/-- **The total complex `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})`**, a cochain complex of finite-order
differential operators on `X ×_S Y / S`: the left-hand side of the de Rham Künneth formula of
[Stacks, Tag 0FMA]. In degree `n` it is the biproduct of the `Ω^p_{X/S} ⊠ Ω^q_{Y/S}` with
`p + q = n`, with differential `d₁ + (-1)^p d₂`. -/
noncomputable def deRhamBoxTotal :
    CochainComplex (FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a)) ℕ :=
  HomologicalComplex.mapBifunctor (deRhamDiffOpComplex a) (deRhamDiffOpComplex b)
    (boxProductCurried a b) (ComplexShape.up ℕ)

/-- The total complex of the box product is the total complex of the double complex. -/
theorem deRhamBoxTotal_eq :
    deRhamBoxTotal a b = (deRhamBoxDoubleComplex a b).total (ComplexShape.up ℕ) :=
  rfl

end AlgebraicGeometry.Scheme.Hom

end
