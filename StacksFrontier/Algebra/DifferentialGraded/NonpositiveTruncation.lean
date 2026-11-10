module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceQuasiIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation

/-! # The degree-`≤ 0` truncation of a differential graded category and of an endomorphism algebra

Let `R` be a commutative ring and let `C` be a differential graded category over `R`
([Stacks, Tag 09L5]). Its *degree-`≤ 0` truncation* `C^{≤0}` has the same objects, and its
degree-`n` morphisms are

* all of `Hom_C(x, y)^n` for `n < 0`,
* the closed ones, `Ker(Hom_C(x, y)^0 → Hom_C(x, y)^1)`, for `n = 0`,
* zero for `n > 0`.

This is again a differential graded category, and the inclusion `C^{≤0} → C` is a functor of
differential graded categories. Applying the endomorphism-algebra construction of
[Stacks, Tag 09LE] to an object `x` in both categories gives differential graded `R`-algebras
`E' = End_{C^{≤0}}(x)` and `E = End_C(x)` together with a homomorphism `E' → E`, and that
homomorphism is a quasi-isomorphism as soon as `E` has no cohomology in positive degrees.

For `C` the differential graded category of right differential graded `B`-modules and `x` a
module `Q`, this is the subalgebra
$$(E')^i = \begin{cases} E^i & i < 0\\ \Ker(E^0 \to E^1) & i = 0\\ 0 & i > 0\end{cases}$$
of the proof of [Stacks, Tag 09SA] (and of [Stacks, Tag 09S8]), together with the first of the
two quasi-isomorphisms `(A, d) ← (E', d) → (E, d)` that proof uses.

## Main definitions

* `DGCategory.nonpositiveHom`: the degree-`n` morphisms of the truncation, as an `R`-submodule
  of the degree-`n` morphisms of `C`.
* `DGCategory.nonpositive`: the degree-`≤ 0` truncation `C^{≤0}`, as a differential graded
  category.
* `DGCategory.nonpositiveInclusion`: the inclusion `C^{≤0} → C`, as a functor of differential
  graded categories.

## Main results

* `DifferentialGradedAlgebra.exists_hom_of_homogeneous`: a homomorphism of differential graded
  algebras can be built from a degreewise family of `R`-linear maps carrying the unit to the
  unit, products of homogeneous elements to products and the differential to the differential.
* `DifferentialGradedAlgebra.exists_hom_of_degreeZero`: a homomorphism out of an algebra with
  nothing in positive degrees into an algebra concentrated in degree zero is determined by, and
  can be built from, a unital multiplicative `R`-linear map on degree-zero parts which kills the
  image of the differential. This is the shape of the second quasi-isomorphism
  `(E', d) → (A, d)` of the proof of [Stacks, Tag 09SA].
* `DifferentialGradedAlgebra.d_eq_zero_of_grading_eq_bot_concentrated` and
  `DifferentialGradedAlgebra.mem_grading_zero_of_grading_eq_bot`: an algebra concentrated in
  degree zero has zero differential and all of its elements are homogeneous of degree zero.
* `DGCategory.exists_hom_algebra_of_dgFunctor`: a functor of differential graded categories
  induces a homomorphism of the endomorphism differential graded algebras of an object, through
  the identifications of [Stacks, Tag 09LE].
* `DGCategory.nonpositive_grading_eq_bot`: the endomorphism algebra of the truncation has nothing
  in positive degrees, so it really is a degree-`≤ 0` algebra.
* `DGCategory.exists_hom_nonpositive_bijective_cohomologyMap`: **the quasi-isomorphism
  `E' → E`.** If every closed homogeneous element of `End_C(x)` of positive degree is a
  coboundary, then the homomorphism `End_{C^{≤0}}(x) → End_C(x)` is bijective on cohomology in
  every degree. This is the input shape of [Stacks, Tag 09S6]
  (`DifferentialGradedModule.derivedExtensionEquivalence`), so it produces an equivalence
  `D(E', d) ≌ D(E, d)`.

## Implementation notes

*Why truncate the category and not the algebra.* The degree-`≤ 0` part of a differential graded
algebra `E` is a graded `R`-subalgebra of `E`, and presenting it as a
`DifferentialGradedAlgebra` would mean producing a `GradedAlgebra` instance — in particular a
direct-sum decomposition — on that subalgebra by hand. Truncating the *category* avoids this
entirely: the endomorphism algebra of an object of a differential graded category is already
built, with its grading and its decomposition, by `DGCategory.homRepresentation` (Tag 09LE), so
`End_{C^{≤0}}(x)` comes with all of that for free and the only thing to check is that the
truncation is a differential graded category. That check is the three closure properties below:
the differential of a closed degree-`0` morphism is zero, and a composite is zero or closed as
soon as one of its factors is.

*What the positivity hypothesis is used for.* Both halves of the cohomology bijection split on
the sign of the degree. In degrees `k > 0` the truncation has nothing, so the hypothesis is
exactly what makes `H^k(E)` vanish too. In degrees `k ≤ 0` the inclusion is bijective on
morphisms of degree `k` and `k - 1` — a morphism of negative degree satisfies the truncation's
condition vacuously, and a closed one of degree `0` satisfies it by assumption — so cocycles and
coboundaries correspond, and no hypothesis is needed.

*The hypothesis is stated on `End_C(x)`, not on an arbitrary presentation.* The statement takes
an arbitrary `DGCategory.HomRepresentation C x` rather than `DGCategory.homRepresentation C x`,
so a caller who already has a named endomorphism algebra of `x` (for instance
`DifferentialGradedModule.endomorphismRepresentation`) can phrase the hypothesis and read the
conclusion in terms of that one.

## References

* [Stacks Project, Tag 09L5](https://stacks.math.columbia.edu/tag/09L5) for differential graded
  categories and [Tag 09L8](https://stacks.math.columbia.edu/tag/09L8) for their functors.
* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for the endomorphism
  differential graded algebra of an object.
* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), whose proof introduces
  this truncation, and [Tag 09S6](https://stacks.math.columbia.edu/tag/09S6), which turns the
  quasi-isomorphism into an equivalence of derived categories.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra R)

/-- **A homomorphism of differential graded algebras from degreewise data.** Given `R`-linear maps
`A^n → B^n` sending the unit to the unit, the product of two homogeneous elements to the product
of their images and the differential to the differential, there is a homomorphism of differential
graded algebras inducing them.

The underlying algebra homomorphism is assembled from the direct-sum decomposition of `A` by
`DirectSum.toAlgebra`; compatibility with the grading is then immediate and compatibility with
the differentials is checked on homogeneous elements. -/
theorem exists_hom_of_homogeneous
    (f : ∀ n : ℤ, A.grading n →ₗ[R] B.grading n)
    (hone : (f 0 ⟨1, SetLike.one_mem_graded A.grading⟩ : B.A) = 1)
    (hmul : ∀ (m n : ℤ) (a : A.grading m) (b : A.grading n),
      (f (m + n) ⟨(a : A.A) * b, SetLike.mul_mem_graded a.property b.property⟩ : B.A) =
        (f m a : B.A) * f n b)
    (hd : ∀ (n : ℤ) (a : A.grading n),
      (f (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ : B.A) = B.d (f n a)) :
    ∃ φ : A.Hom B, ∀ (n : ℤ) (a : A.grading n), φ.toAlgebraHom a = f n a := by
  let g (n : ℤ) := (B.grading n).subtype.comp (f n)
  let φ : A.A →ₐ[R] B.A :=
    (DirectSum.toAlgebra R (fun n => A.grading n) g hone (fun {m n} a b => hmul m n a b)).comp
      (DirectSum.decomposeAlgEquiv A.grading).toAlgHom
  have hφ (n : ℤ) (a : A.grading n) : φ a = (f n a : B.A) := by
    change DirectSum.toModule R ℤ B.A g (DirectSum.decomposeLinearEquiv A.grading a) = _
    rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
    rfl
  refine ⟨{ toAlgebraHom := φ, map_grading := ?_, map_d := ?_ }, hφ⟩
  · intro n a ha
    rw [hφ n ⟨a, ha⟩]
    exact (f n ⟨a, ha⟩).property
  · intro a
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | @homogeneous n a =>
      calc
        φ (A.d a) = f (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ :=
          hφ (n + 1) ⟨A.d a, A.d_mem n a a.property⟩
        _ = B.d (f n a) := hd n a
        _ = B.d (φ a) := congrArg B.d (hφ n a).symm
    | add a b ha hb => simp only [map_add, ha, hb]

/-- A homogeneous element of a degree in which the algebra vanishes is zero. -/
private theorem coe_eq_zero_of_grading_eq_bot {i : ℤ} (hi : A.grading i = ⊥) (x : A.grading i) :
    (x : A.A) = 0 :=
  (Submodule.mem_bot R).mp (hi ▸ x.property)

/-- A differential graded algebra with nothing outside degree zero has zero differential: the
differential of a degree-zero element is of degree one, hence zero, and every other homogeneous
element is itself zero. -/
theorem d_eq_zero_of_grading_eq_bot_concentrated (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) (x : A.A) :
    A.d x = 0 := by
  induction x using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | @homogeneous i x =>
    by_cases hi : i = 0
    · subst i
      refine (Submodule.mem_bot R).mp ?_
      rw [← hA 1 (by norm_num)]
      simpa using A.d_mem 0 (x : A.A) x.property
    · rw [A.coe_eq_zero_of_grading_eq_bot (hA i hi) x, map_zero]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Every element of a differential graded algebra with nothing outside degree zero is homogeneous
of degree zero. -/
theorem mem_grading_zero_of_grading_eq_bot (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) (x : A.A) :
    x ∈ A.grading 0 := by
  induction x using DirectSum.Decomposition.inductionOn A.grading with
  | zero => exact (A.grading 0).zero_mem
  | @homogeneous i x =>
    by_cases hi : i = 0
    · subst i
      exact x.property
    · rw [A.coe_eq_zero_of_grading_eq_bot (hA i hi) x]
      exact (A.grading 0).zero_mem
  | add x y hx hy => exact (A.grading 0).add_mem hx hy

/-- **A homomorphism from a degree-`≤ 0` algebra into a degree-`0` algebra, from its degree-zero
part.** Let `A` have nothing in positive degrees and let `B` have nothing outside degree zero.
A map `A^0 → B` which is `R`-linear, unital, multiplicative and kills the image of the
differential `A^{-1} → A^0` extends to a homomorphism of differential graded algebras `A → B`,
necessarily zero in every nonzero degree.

This is the shape of the second quasi-isomorphism `(E', d) → (A, d)` of the proof of
[Stacks, Tag 09SA]: there `A = H^0(A)` is concentrated in degree zero, `E'` is the degree-`≤ 0`
truncation of `End(P)`, and the map on degree-zero parts is `Z^0(End(P)) → H^0(End(P)) = A`.
What the hypothesis `hd` says is exactly that the map factors through the degree-zero
cohomology. -/
theorem exists_hom_of_degreeZero
    (hA : ∀ n : ℤ, 0 < n → A.grading n = ⊥) (hB : ∀ n : ℤ, n ≠ 0 → B.grading n = ⊥)
    (f : A.grading 0 →ₗ[R] B.A)
    (hone : f ⟨1, SetLike.one_mem_graded A.grading⟩ = 1)
    (hmul : ∀ a b : A.grading 0,
      f ⟨(a : A.A) * b, SetLike.mul_mem_graded a.property b.property⟩ = f a * f b)
    (hd : ∀ a : A.grading (-1),
      f ⟨A.d a, by simpa using A.d_mem (-1) a a.property⟩ = 0) :
    ∃ φ : A.Hom B,
      (∀ a : A.grading 0, φ.toAlgebraHom a = f a) ∧
        ∀ (n : ℤ), n ≠ 0 → ∀ a : A.grading n, φ.toAlgebraHom a = 0 := by
  classical
  let g (n : ℤ) : A.grading n →ₗ[R] B.grading n :=
    if hn : n = 0 then
      hn ▸ f.codRestrict (B.grading 0) fun a => mem_grading_zero_of_grading_eq_bot B hB (f a)
    else 0
  have gzero (a : A.grading 0) : (g 0 a : B.A) = f a := by simp [g]
  have gne (n : ℤ) (hn : n ≠ 0) (a : A.grading n) : (g n a : B.A) = 0 := by simp [g, hn]
  have apos {n : ℤ} (hn : 0 < n) (a : A.grading n) : a = 0 :=
    Subtype.ext (A.coe_eq_zero_of_grading_eq_bot (hA n hn) a)
  have hmul' (m n : ℤ) (a : A.grading m) (b : A.grading n) :
      (g (m + n) ⟨(a : A.A) * b, SetLike.mul_mem_graded a.property b.property⟩ : B.A) =
        (g m a : B.A) * g n b := by
    by_cases hm : 0 < m
    · rw [apos hm a]
      simp only [Submodule.coe_zero, zero_mul, map_zero]
      exact congrArg Subtype.val (map_zero (g (m + n)))
    by_cases hn : 0 < n
    · rw [apos hn b]
      simp only [Submodule.coe_zero, mul_zero, map_zero]
      exact congrArg Subtype.val (map_zero (g (m + n)))
    by_cases hs : m + n = 0
    · obtain rfl : m = 0 := by omega
      obtain rfl : n = 0 := by omega
      rw [gzero a, gzero b, ← hmul a b]
      exact gzero ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩
    rw [gne (m + n) hs]
    by_cases hm0 : m = 0
    · rw [gne n (by omega), mul_zero]
    · rw [gne m hm0, zero_mul]
  have hd' (n : ℤ) (a : A.grading n) :
      (g (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ : B.A) = B.d (g n a) := by
    rw [d_eq_zero_of_grading_eq_bot_concentrated B hB]
    by_cases hn : n + 1 = 0
    · obtain rfl : n = -1 := by omega
      exact (gzero _).trans (hd a)
    · exact gne (n + 1) hn _
  obtain ⟨φ, hφ⟩ := A.exists_hom_of_homogeneous B g ((gzero _).trans hone) hmul' hd'
  exact ⟨φ, fun a => (hφ 0 a).trans (gzero a), fun n hn a => (hφ n a).trans (gne n hn a)⟩

end DifferentialGradedAlgebra

namespace DGCategory

variable {R : Type u} [CommRing R]

/-! ### The degree-`≤ 0` truncation of a differential graded category -/

/-- The degree-`n` morphisms `x ⟶ y` of the degree-`≤ 0` truncation of `C`: all of them for
`n < 0`, the closed ones for `n = 0`, and none for `n > 0`. -/
def nonpositiveHom (C : DGCategory.{w, v, u} R) (x y : C.Obj) (n : ℤ) :
    Submodule R (C.Hom x y n) where
  carrier := { f | (0 < n → f = 0) ∧ (n = 0 → C.d f = 0) }
  zero_mem' := ⟨fun _ => rfl, fun _ => C.d_zero⟩
  add_mem' {f g} hf hg :=
    ⟨fun hn => by rw [hf.1 hn, hg.1 hn, add_zero],
      fun hn => by rw [C.d_add, hf.2 hn, hg.2 hn, add_zero]⟩
  smul_mem' r f hf :=
    ⟨fun hn => by rw [hf.1 hn, smul_zero], fun hn => by rw [C.d_smul, hf.2 hn, smul_zero]⟩

/-- The differential of the truncation: the differential of `C`, which lands in the truncation
because the differential of a closed degree-`0` morphism is zero and the differential of zero is
zero. -/
def nonpositiveHomDifferential (C : DGCategory.{w, v, u} R) {x y : C.Obj} {n : ℤ}
    (f : nonpositiveHom C x y n) : nonpositiveHom C x y (n + 1) :=
  ⟨C.d f.1, by
    refine ⟨fun hn => ?_, fun _ => C.d_d f.1⟩
    by_cases h : n = 0
    · exact f.2.2 h
    · rw [f.2.1 (by omega), C.d_zero]⟩

/-- Composition in the truncation: composition in `C`, which lands in the truncation because a
composite with a factor of positive degree has a zero factor, and a composite of two closed
degree-`0` morphisms is closed by the Leibniz rule. -/
def nonpositiveHomComp (C : DGCategory.{w, v, u} R) {x y z : C.Obj} {m n k : ℤ}
    (h : m + n = k) (g : nonpositiveHom C y z m) (f : nonpositiveHom C x y n) :
    nonpositiveHom C x z k :=
  ⟨C.comp h g.1 f.1, by
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · by_cases hm : 0 < m
      · rw [g.2.1 hm, C.comp_zero_left]
      · rw [f.2.1 (by omega), C.comp_zero_right]
    · by_cases hm : 0 < m
      · rw [g.2.1 hm, C.comp_zero_left, C.d_zero]
      by_cases hn : 0 < n
      · rw [f.2.1 hn, C.comp_zero_right, C.d_zero]
      rw [C.leibniz, g.2.2 (by omega), f.2.2 (by omega), C.comp_zero_left,
        C.comp_zero_right, smul_zero, add_zero]⟩

/-- **The degree-`≤ 0` truncation `C^{≤0}` of a differential graded category `C`.** It has the
objects of `C`, and `DGCategory.nonpositiveHom` as its morphisms; every axiom is inherited from
`C`, the closure of the truncation under the differential and under composition being
`DGCategory.nonpositiveHomDifferential` and `DGCategory.nonpositiveHomComp`. The identity of an
object is closed of degree `0`, so it belongs to the truncation. -/
@[implicit_reducible]
def nonpositive (C : DGCategory.{w, v, u} R) : DGCategory.{w, v, u} R where
  Obj := C.Obj
  Hom x y n := nonpositiveHom C x y n
  addCommGroup _ _ _ := inferInstance
  module _ _ _ := inferInstance
  d := nonpositiveHomDifferential C
  d_add f g := Subtype.ext (C.d_add f.1 g.1)
  d_smul r f := Subtype.ext (C.d_smul r f.1)
  d_d f := Subtype.ext (C.d_d f.1)
  comp := nonpositiveHomComp C
  comp_add_left h g₁ g₂ f := Subtype.ext (C.comp_add_left h g₁.1 g₂.1 f.1)
  comp_add_right h g f₁ f₂ := Subtype.ext (C.comp_add_right h g.1 f₁.1 f₂.1)
  comp_smul_left h r g f := Subtype.ext (C.comp_smul_left h r g.1 f.1)
  comp_smul_right h r g f := Subtype.ext (C.comp_smul_right h r g.1 f.1)
  leibniz h g f := Subtype.ext (C.leibniz h g.1 f.1)
  assoc h₁ h₂ h₃ h₄ e g f := Subtype.ext (C.assoc h₁ h₂ h₃ h₄ e.1 g.1 f.1)
  id x := ⟨C.id x, fun h => absurd h (lt_irrefl 0), fun _ => C.d_id x⟩
  id_comp f := Subtype.ext (C.id_comp f.1)
  comp_id f := Subtype.ext (C.comp_id f.1)
  d_id x := Subtype.ext (C.d_id x)

/-- **The inclusion `C^{≤0} → C`**, a functor of differential graded categories: the identity on
objects and the inclusion of submodules on morphisms. Every compatibility holds by
definition. -/
def nonpositiveInclusion (C : DGCategory.{w, v, u} R) : DGFunctor (nonpositive C) C where
  obj x := x
  map f := f.1
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_d _ := rfl
  map_comp _ _ _ := rfl
  map_id _ := rfl

/-! ### The induced homomorphism of endomorphism algebras -/

variable {C D : DGCategory.{w, v, u} R}

/-- The unit of the endomorphism algebra of `x` is the identity of `x`, with the unit written as
a homogeneous element rather than extracted from the existence statement. -/
theorem HomRepresentation.algebraHom_one {x : C.Obj} (S : HomRepresentation C x) :
    S.algebraHom 0 ⟨1, SetLike.one_mem_graded S.algebra.grading⟩ = C.id x := by
  obtain ⟨e, he, hid⟩ := S.algebra_one
  have he' : e = ⟨1, SetLike.one_mem_graded S.algebra.grading⟩ := Subtype.ext he
  simpa only [he'] using hid

/-- Multiplication in the endomorphism algebra of `x` is composition in `C`, with the product
written as a homogeneous element rather than extracted from the existence statement. -/
theorem HomRepresentation.algebraHom_mul {x : C.Obj} (S : HomRepresentation C x) (m n : ℤ)
    (a : S.algebra.grading m) (b : S.algebra.grading n) :
    S.algebraHom (m + n) ⟨(a : S.algebra.A) * b,
        SetLike.mul_mem_graded a.property b.property⟩ =
      C.comp rfl (S.algebraHom m a) (S.algebraHom n b) := by
  obtain ⟨c, hc, hcomp⟩ := S.algebra_mul m n (m + n) rfl a b
  have hc' : c = ⟨(a : S.algebra.A) * b,
      SetLike.mul_mem_graded a.property b.property⟩ := Subtype.ext hc
  simpa only [hc'] using hcomp

/-- **A functor of differential graded categories induces a homomorphism of endomorphism
differential graded algebras.** For `F : C → D` a functor of differential graded categories, `x`
an object of `C`, and endomorphism algebras `S` of `x` and `T` of `F x` as in [Stacks, Tag 09LE],
there is a homomorphism `S.algebra → T.algebra` which under the identifications of the two
algebras with the homogeneous endomorphisms is `F` itself.

The degreewise map is `F` conjugated by the two identifications; it preserves the unit, products
and the differential because `F` does, which is what
`DifferentialGradedAlgebra.exists_hom_of_homogeneous` needs. -/
theorem exists_hom_algebra_of_dgFunctor (F : DGFunctor C D) {x : C.Obj}
    (S : HomRepresentation C x) (T : HomRepresentation D (F.obj x)) :
    ∃ φ : S.algebra.Hom T.algebra,
      ∀ (n : ℤ) (a : S.algebra.grading n),
        T.algebraHom n ⟨φ.toAlgebraHom a, φ.map_grading n a a.property⟩ =
          F.map (S.algebraHom n a) := by
  let f (n : ℤ) : S.algebra.grading n →ₗ[R] T.algebra.grading n :=
    { toFun a := (T.algebraHom n).symm (F.map (S.algebraHom n a))
      map_add' a b := by simp only [map_add, F.map_add]
      map_smul' r a := by simp only [map_smul, F.map_smul, RingHom.id_apply] }
  -- `f n a` is the element of `T` which `T.algebraHom n` sends to `F (S.algebraHom n a)`.
  have hf (n : ℤ) (a : S.algebra.grading n) (b : T.algebra.grading n)
      (h : F.map (S.algebraHom n a) = T.algebraHom n b) : (f n a : T.algebra.A) = b :=
    congrArg Subtype.val ((LinearEquiv.symm_apply_eq _).mpr h)
  have hone : (f 0 ⟨1, SetLike.one_mem_graded S.algebra.grading⟩ : T.algebra.A) = 1 :=
    hf 0 _ ⟨1, SetLike.one_mem_graded T.algebra.grading⟩
      (by rw [HomRepresentation.algebraHom_one, HomRepresentation.algebraHom_one, F.map_id])
  have hmul (m n : ℤ) (a : S.algebra.grading m) (b : S.algebra.grading n) :
      (f (m + n) ⟨(a : S.algebra.A) * b,
          SetLike.mul_mem_graded a.property b.property⟩ : T.algebra.A) =
        (f m a : T.algebra.A) * f n b :=
    hf (m + n) _ ⟨(f m a : T.algebra.A) * f n b,
        SetLike.mul_mem_graded (f m a).property (f n b).property⟩ (by
      rw [HomRepresentation.algebraHom_mul, HomRepresentation.algebraHom_mul, F.map_comp]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply])
  have hd (n : ℤ) (a : S.algebra.grading n) :
      (f (n + 1) ⟨S.algebra.d a, S.algebra.d_mem n a a.property⟩ : T.algebra.A) =
        T.algebra.d (f n a) :=
    hf (n + 1) _ ⟨T.algebra.d (f n a), T.algebra.d_mem n (f n a) (f n a).property⟩ (by
      rw [S.algebra_d, T.algebra_d, F.map_d]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply])
  obtain ⟨φ, hφ⟩ := S.algebra.exists_hom_of_homogeneous T.algebra f hone hmul hd
  refine ⟨φ, fun n a => ?_⟩
  have h : (⟨φ.toAlgebraHom a, φ.map_grading n a a.property⟩ : T.algebra.grading n) =
      f n a := Subtype.ext (hφ n a)
  rw [h]
  exact (T.algebraHom n).apply_symm_apply _

/-! ### The quasi-isomorphism `End_{C^{≤0}}(x) → End_C(x)` -/

/-- The endomorphism algebra of an object of the degree-`≤ 0` truncation has nothing in positive
degrees. -/
theorem nonpositive_grading_eq_bot (C : DGCategory.{w, v, u} R) (x : C.Obj) (n : ℤ)
    (hn : 0 < n) : (homRepresentation (nonpositive C) x).algebra.grading n = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun a ha => congrArg Subtype.val
    (((homRepresentation (nonpositive C) x).algebraHom n).map_eq_zero_iff.mp
      (Subtype.ext (((homRepresentation (nonpositive C) x).algebraHom n ⟨a, ha⟩).2.1 hn)))

/-- **The quasi-isomorphism `End_{C^{≤0}}(x) → End_C(x)`.** Let `C` be a differential graded
category over `R`, let `x` be an object of `C` and let `H` present the endomorphism differential
graded algebra `E = End_C(x)` of `x` as in [Stacks, Tag 09LE]. Assume that every closed
homogeneous element of `E` of positive degree is a coboundary, i.e. `H^k(E) = 0` for `k > 0`.
Then the homomorphism `End_{C^{≤0}}(x) → E` of
`DGCategory.exists_hom_algebra_of_dgFunctor` applied to `DGCategory.nonpositiveInclusion` is
bijective on cohomology in every degree.

This is the first of the two quasi-isomorphisms `(A, d) ← (E', d) → (E, d)` in the proof of
[Stacks, Tag 09SA]; the hypothesis is the vanishing of `H^k(E)` for `k > 0` that proof deduces
from `A = H^0(A)`. Composed with
`DifferentialGradedModule.derivedExtensionEquivalence` ([Stacks, Tag 09S6]) it gives an
equivalence `D(E', d) ≌ D(E, d)`.

In degrees `k > 0` both sides vanish: the truncation has no morphisms there
(`DGCategory.nonpositive_grading_eq_bot`) and `H^k(E) = 0` by hypothesis. In degrees `k ≤ 0` the
inclusion is bijective in degrees `k` and `k - 1` — a morphism of negative degree lies in the
truncation for free, and a closed degree-`0` one lies in it by being closed — so cocycles and
coboundaries match up. -/
theorem exists_hom_nonpositive_bijective_cohomologyMap (C : DGCategory.{w, v, u} R) (x : C.Obj)
    (H : HomRepresentation C x)
    (hpos : ∀ n : ℤ, 0 < n → ∀ a : H.algebra.grading n, H.algebra.d a = 0 →
      ∃ c : H.algebra.grading (n - 1), (a : H.algebra.A) = H.algebra.d c) :
    ∃ φ : (homRepresentation (nonpositive C) x).algebra.Hom H.algebra,
      ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k) := by
  set S := homRepresentation (nonpositive C) x with hS
  obtain ⟨φ, hφ⟩ := exists_hom_algebra_of_dgFunctor (nonpositiveInclusion C) S H
  -- `φ` is injective in every degree, since it is `F` read through two linear equivalences.
  have hinj (n : ℤ) (a b : S.algebra.grading n)
      (hab : φ.toAlgebraHom a = φ.toAlgebraHom b) : a = b := by
    have he : (⟨φ.toAlgebraHom a, φ.map_grading n a a.property⟩ : H.algebra.grading n) =
        ⟨φ.toAlgebraHom b, φ.map_grading n b b.property⟩ := Subtype.ext hab
    exact (S.algebraHom n).injective
      (Subtype.ext ((hφ n a).symm.trans ((congrArg (H.algebraHom n) he).trans (hφ n b))))
  -- A homogeneous element of `E` satisfying the truncation's condition is in the image of `φ`.
  have hlift (n : ℤ) (a : H.algebra.grading n)
      (hg : (0 < n → H.algebraHom n a = 0) ∧ (n = 0 → C.d (H.algebraHom n a) = 0)) :
      ∃ b : S.algebra.grading n, φ.toAlgebraHom b = a := by
    refine ⟨(S.algebraHom n).symm ⟨H.algebraHom n a, hg⟩, ?_⟩
    have hh := hφ n ((S.algebraHom n).symm ⟨H.algebraHom n a, hg⟩)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact congrArg Subtype.val ((H.algebraHom n).injective hh)
  -- A closed homogeneous element of `E` of degree `≤ 0` satisfies the truncation's condition.
  have hclosed (n : ℤ) (a : H.algebra.grading n) (ha : H.algebra.d a = 0) :
      C.d (H.algebraHom n a) = 0 := by
    rw [← H.algebra_d]
    have h : (⟨H.algebra.d a, H.algebra.d_mem n a a.property⟩ :
        H.algebra.grading (n + 1)) = 0 := Subtype.ext ha
    rw [h, map_zero]
  refine ⟨φ, fun k => ⟨?_, ?_⟩⟩
  · intro X Y hXY
    induction X using Quotient.ind with | _ a => ?_
    induction Y using Quotient.ind with | _ b => ?_
    rw [DifferentialGradedAlgebra.Hom.cohomologyMap_mk,
      DifferentialGradedAlgebra.Hom.cohomologyMap_mk] at hXY
    obtain ⟨c, hc⟩ := Quotient.exact hXY
    rw [DifferentialGradedAlgebra.Hom.cocycleMap_val,
      DifferentialGradedAlgebra.Hom.cocycleMap_val] at hc
    by_cases hk : 0 < k
    · refine Quotient.sound ⟨0, ?_⟩
      have hab (y : S.algebra.Cocycle k) : (y.1 : S.algebra.A) = 0 :=
        S.algebra.coe_eq_zero_of_grading_eq_bot (nonpositive_grading_eq_bot C x k hk) y.1
      rw [hab a, hab b, sub_self, Submodule.coe_zero, map_zero]
    · obtain ⟨e, he⟩ := hlift (k - 1) c ⟨fun h => absurd (by omega : 0 < k) hk,
        fun h => absurd (by omega : 0 < k) hk⟩
      refine Quotient.sound ⟨e, ?_⟩
      refine congrArg Subtype.val (hinj k (a.1 - b.1)
        ⟨S.algebra.d e, by simpa using S.algebra.d_mem (k - 1) e e.property⟩ ?_)
      change φ.toAlgebraHom ((a.1 : S.algebra.A) - b.1) = φ.toAlgebraHom (S.algebra.d e)
      rw [map_sub, φ.map_d, he]
      exact hc
  · intro X
    induction X using Quotient.ind with | _ a => ?_
    by_cases hk : 0 < k
    · obtain ⟨c, hc⟩ := hpos k hk a.1 a.2
      refine ⟨Quotient.mk _ ⟨0, by rw [Submodule.coe_zero, map_zero]⟩,
        Quotient.sound ⟨-c, ?_⟩⟩
      rw [DifferentialGradedAlgebra.Hom.cocycleMap_val, Submodule.coe_zero, map_zero, zero_sub,
        Submodule.coe_neg, map_neg, hc]
    · obtain ⟨b, hb⟩ := hlift k a.1 ⟨fun h => absurd h hk, fun _ => hclosed k a.1 a.2⟩
      have hdb : S.algebra.d b = 0 := by
        refine congrArg Subtype.val (hinj (k + 1)
          ⟨S.algebra.d b, S.algebra.d_mem k b b.property⟩ 0 ?_)
        change φ.toAlgebraHom (S.algebra.d b) = φ.toAlgebraHom ((0 : S.algebra.grading (k + 1)))
        rw [φ.map_d, hb, a.2, Submodule.coe_zero, map_zero]
      refine ⟨Quotient.mk _ ⟨b, hdb⟩, Quotient.sound ⟨0, ?_⟩⟩
      rw [DifferentialGradedAlgebra.Hom.cocycleMap_val, hb, sub_self, Submodule.coe_zero,
        map_zero]

end DGCategory

end
