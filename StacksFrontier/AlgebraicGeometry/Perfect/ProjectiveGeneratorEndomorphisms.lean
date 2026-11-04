module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Complex

/-!
# The upper triangular matrix algebra acting on the twist sum on projective space

Let `A` be a commutative ring, let `S = A[X₀, …, Xₙ]` graded by total degree and let
`X = ℙⁿ_A = Proj(S)`. The object

`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`

and the upper triangular matrix algebra `R` whose `(i, j)` entry is homogeneous of degree
`j - i` are the two sides of the displayed equation `R = Hom_{𝒪_X}(P, P)` of
[Stacks, Tag 0CS9]. This file builds the comparison map of that equation: multiplication by the
`(i, j)` entry is a morphism `𝒪_X(-j) ⟶ 𝒪_X(-i)`, and the resulting matrix of morphisms is a
ring homomorphism

`R ⟶ End(P)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul`: multiplication by an element of
  integer degree `c`, as a morphism `𝒪(d) ⟶ 𝒪(e)` of twisting sheaves on `Proj S` for any
  integers with `c + d = e`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.projTwistSum`: the direct sum
  `𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` on `X = Proj A[X₀, …, Xₙ]`.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixEntryHom`: the morphism
  `𝒪_X(-j) ⟶ 𝒪_X(-i)` given by the `(i, j)` entry of a matrix of the algebra.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixToEnd`: **the comparison ring
  homomorphism** `R →+* End(P)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul_comp`: multiplication morphisms compose
  by multiplying the elements, in every pair of integer degrees.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul_one`,
  `twistMul_add`, `twistMul_zero`: multiplication by `1` is the identity, multiplication is
  additive in the element and multiplication by `0` is the zero morphism.
* `Stacks.AlgebraicGeometry.ProjectiveGenerator.components_matrixToEnd`: the `(i, j)` component
  of the endomorphism attached to a matrix is multiplication by its `(i, j)` entry.

That the comparison map is an isomorphism is
`Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixRingEquivEnd`, in
`StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveGeneratorHomGroups.lean`, which identifies each
group `Hom(𝒪(-j), 𝒪(-i))` with `S_{j-i}`.

## Implementation notes

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistMulLeftIntOf` takes a homogeneous element of a
*natural-number* degree, so it cannot express an entry below the diagonal, where the degree
`j - i` is negative and the entry is zero. `twistMul` below is the same construction with the
degree of the element an integer, taken in
`AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`, which is the zero submodule in
negative
degrees; the single construction then covers every entry of the matrix with no case split, and
the composition law needs no split either because its proof is pointwise multiplication in a
localization and never mentions the degree.

The twist sum is formed on `Proj A[X₀, …, Xₙ]`, which is the scheme `X = ℙⁿ_A = Proj(S)` of the
Stacks statement.

## References

* [Stacks Project, Tag 0CS9](https://stacks.math.columbia.edu/tag/0CS9)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.AlgebraicGeometry.ProjectiveGenerator

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Multiplication by an element of integer degree -/

section TwistMul

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The integer-extended grading is multiplicative.** In a negative degree the piece is the
zero submodule, so the only case with content is the one where both degrees are nonnegative,
where this is `SetLike.mul_mem_graded`. -/
public theorem mul_mem_integerGrading' {i j : ℤ} {x y : S}
    (hx : x ∈ integerGrading (S := S) 𝒮 i) (hy : y ∈ integerGrading (S := S) 𝒮 j) :
    x * y ∈ integerGrading (S := S) 𝒮 (i + j) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [integerGrading_neg _ _ hi, Submodule.mem_bot] at hx
    simp [hx]
  rcases lt_or_ge j 0 with hj | hj
  · rw [integerGrading_neg _ _ hj, Submodule.mem_bot] at hy
    simp [hy]
  lift i to ℕ using hi
  lift j to ℕ using hj
  rw [integerGrading_natCast, mem_homogeneousSubmodule] at hx hy
  rw [← Nat.cast_add, integerGrading_natCast, mem_homogeneousSubmodule]
  exact SetLike.mul_mem_graded hx hy

/-- Multiplication by an element `p` of integer degree `c`, as a morphism
`𝒪_{Proj 𝒮}(d) ⟶ 𝒪_{Proj 𝒮}(e)` of twisting sheaves, where `e` is any integer equal to
`c + d`. The degree is taken in `integerGrading`, which is
zero in negative degrees, so a negative `c` forces `p = 0` and the morphism is the zero map. -/
public def twistMul (p : S) (c d e : ℤ) (hp : p ∈ integerGrading 𝒮 c) (he : c + d = e) :
    twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap 𝒮
    (twistGrading (S := S) 𝒮 d) (twistGrading (S := S) 𝒮 e)
    (LinearMap.mulLeft S p) <| by
      intro j y hy
      have h := mul_mem_integerGrading' 𝒮 (j := j + d) hp hy
      rwa [show c + (j + d) = j + e by omega] at h

/-- Multiplication by `p` acts on a section fibrewise, as the localization of multiplication by
`p` at each homogeneous prime. -/
public theorem twistMul_apply (p : S) (c d e : ℤ) (hp : p ∈ integerGrading 𝒮 c)
    (he : c + d = e) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twistingSheaf 𝒮 d).val.obj U) (x : U.unop) :
    ((twistMul 𝒮 p c d e hp he).val.app U s).1 x =
      LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
        (LinearMap.mulLeft S p) (s.1 x) :=
  rfl

/-- Localized multiplication by two ring elements in turn is localized multiplication by their
product. -/
private theorem map_mulLeft_map_mulLeft {P : Submonoid S} (v v' : S)
    (z : LocalizedModule P S) :
    LocalizedModule.map P (LinearMap.mulLeft S v)
        (LocalizedModule.map P (LinearMap.mulLeft S v') z) =
      LocalizedModule.map P (LinearMap.mulLeft S (v * v')) z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
    exact congrArg (fun y => LocalizedModule.mk y s) (mul_assoc v v' m).symm

/-- Two morphisms of twisting sheaves agree as soon as they agree on the value of every section
at every point. -/
private theorem twist_hom_ext {d e : ℤ} (φ ψ : twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e)
    (h : ∀ (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (s : (twistingSheaf 𝒮 d).val.obj U)
      (x : U.unop), (φ.val.app U s).1 x = (ψ.val.app U s).1 x) : φ = ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  exact Subtype.ext (funext fun x => h U s x)

/-- **Multiplication morphisms compose by multiplying the elements**, in every pair of integer
degrees. -/
public theorem twistMul_comp (p q : S) (c c' d e g : ℤ) (hp : p ∈ integerGrading 𝒮 c)
    (hq : q ∈ integerGrading 𝒮 c') (he : c + d = e) (hg : c' + e = g) :
    twistMul 𝒮 p c d e hp he ≫ twistMul 𝒮 q c' e g hq hg =
      twistMul 𝒮 (q * p) (c' + c) d g (mul_mem_integerGrading' 𝒮 hq hp)
        (by omega) :=
  twist_hom_ext 𝒮 _ _ fun _ _ _ => map_mulLeft_map_mulLeft q p _

/-- **Multiplication by `1` is the identity.** -/
public theorem twistMul_one (d : ℤ) (h1 : (1 : S) ∈ integerGrading 𝒮 0) :
    twistMul 𝒮 1 0 d d h1 (zero_add d) = CategoryStruct.id (twistingSheaf 𝒮 d) :=
  twist_hom_ext 𝒮 _ _ fun U s x => by
    rw [twistMul_apply, show LinearMap.mulLeft S (1 : S) = LinearMap.id from
      LinearMap.ext fun y => one_mul y, LocalizedModule.map_id]
    rfl

/-- **Multiplication is additive in the element.** -/
public theorem twistMul_add (p q : S) (c d e : ℤ) (hp : p ∈ integerGrading 𝒮 c)
    (hq : q ∈ integerGrading 𝒮 c) (he : c + d = e) :
    twistMul 𝒮 (p + q) c d e (add_mem hp hq) he =
      twistMul 𝒮 p c d e hp he + twistMul 𝒮 q c d e hq he :=
  twist_hom_ext 𝒮 _ _ fun U s x => by
    rw [twistMul_apply, show LinearMap.mulLeft S (p + q) =
      LinearMap.mulLeft S p + LinearMap.mulLeft S q from LinearMap.ext fun y => add_mul p q y,
      map_add, LinearMap.add_apply]
    rfl

/-- **Multiplication by `0` is the zero morphism.** -/
public theorem twistMul_zero (c d e : ℤ) (he : c + d = e) :
    twistMul 𝒮 0 c d e (zero_mem _) he = 0 :=
  twist_hom_ext 𝒮 _ _ fun U s x => by
    rw [twistMul_apply, show LinearMap.mulLeft S (0 : S) = 0 from
      LinearMap.ext fun y => zero_mul y, map_zero]
    rfl

/-- The unit is homogeneous of degree zero for the integer-extended grading. -/
public theorem one_mem_integerGrading : (1 : S) ∈ integerGrading 𝒮 0 := by
  have h := integerGrading_natCast 𝒮 0
  rw [Nat.cast_zero] at h
  rw [h, mem_homogeneousSubmodule]
  exact SetLike.one_mem_graded 𝒮

/-- Multiplication by equal elements agrees, whatever degree each is certified in: the degree
enters the construction only through a proof. -/
public theorem twistMul_congr {p q : S} {c c' d e : ℤ} (hp : p ∈ integerGrading 𝒮 c)
    (hq : q ∈ integerGrading 𝒮 c') (he : c + d = e) (he' : c' + d = e) (h : p = q) :
    twistMul 𝒮 p c d e hp he = twistMul 𝒮 q c' d e hq he' := by
  subst h
  rfl

/-- **Multiplication as an additive map** out of the degree-`c` piece: the packaging of
`twistMul` that makes a finite sum of entries go through it. -/
public def twistMulHom (c d e : ℤ) (he : c + d = e) :
    integerGrading 𝒮 c →+ (twistingSheaf 𝒮 d ⟶ twistingSheaf 𝒮 e) where
  toFun p := twistMul 𝒮 p.1 c d e p.2 he
  map_zero' := twistMul_zero 𝒮 c d e he
  map_add' p q := twistMul_add 𝒮 p.1 q.1 c d e p.2 q.2 he

/-- `twistMulHom` sends an element `p` of the degree-`c` piece to multiplication by `p`. -/
@[simp] public theorem twistMulHom_apply (c d e : ℤ) (he : c + d = e)
    (p : integerGrading 𝒮 c) :
    twistMulHom 𝒮 c d e he p = twistMul 𝒮 p.1 c d e p.2 he := rfl

end TwistMul

/-! ### The twist sum on `Proj A[X₀, …, Xₙ]` and the comparison with the matrix algebra -/

section Matrices

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The family `𝒪_X, 𝒪_X(-1), …, 𝒪_X(-n)` of nonpositive twists on
`X = ℙⁿ_A = Proj A[X₀, …, Xₙ]`. -/
public abbrev twistFamily :
    Fin (n + 1) → SheafOfModules.{u} (projRingSheaf (polyGrading A n)) :=
  fun i => twistingSheaf (polyGrading A n) (-(i : ℤ))

/-- **The twist sum `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`** on `X = ℙⁿ_A = Proj A[X₀, …, Xₙ]`,
the perfect generator of the displayed equation of [Stacks, Tag 0CS8] read on the `Proj`
model. -/
public abbrev projTwistSum : SheafOfModules.{u} (projRingSheaf (polyGrading A n)) :=
  ⨁ twistFamily A n

/-- Membership in the degree-`d` piece of `homogeneousPiece` and of the integer-extended grading
of `Proj` agree. -/
private theorem mem_homogeneousPiece_iff_mem_integerGrading {d : ℤ}
    {p : MvPolynomial (Fin (n + 1)) A} :
    p ∈ homogeneousPiece A n d ↔ p ∈ integerGrading (polyGrading A n) d := by
  rcases lt_or_ge d 0 with hd | hd
  · rw [integerGrading_neg _ _ hd, homogeneousPiece_of_neg A n hd, Submodule.mem_bot,
      Submodule.mem_bot]
  · have h := integerGrading_natCast (polyGrading A n) d.toNat
    rw [Int.toNat_of_nonneg hd] at h
    rw [h, mem_homogeneousSubmodule, homogeneousPiece_of_nonneg A n hd]

/-- A polynomial in the degree-`d` piece of
`Stacks.AlgebraicGeometry.ProjectiveGenerator.homogeneousPiece` lies in the degree-`d` piece of
the integer-extended grading that the twists on `Proj` are built from. The two are the same
submodule read over two base rings. -/
public theorem mem_integerGrading_of_mem_homogeneousPiece {d : ℤ}
    {p : MvPolynomial (Fin (n + 1)) A} (hp : p ∈ homogeneousPiece A n d) :
    p ∈ integerGrading (polyGrading A n) d := (mem_homogeneousPiece_iff_mem_integerGrading A n).1 hp

/-- The product of the `(i, k)` entry of one matrix of the algebra and the `(k, j)` entry of
another is homogeneous of degree `j - i`. -/
public theorem entry_mul_mem (M N : endomorphismMatrices A n) (i j k : Fin (n + 1)) :
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)) i k *
        (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)) k j ∈
      integerGrading (polyGrading A n) ((j : ℤ) - (i : ℤ)) := by
  have h := mul_mem_integerGrading' (polyGrading A n)
    (mem_integerGrading_of_mem_homogeneousPiece A n (M.2 i k))
    (mem_integerGrading_of_mem_homogeneousPiece A n (N.2 k j))
  rwa [show ((k : ℤ) - (i : ℤ)) + ((j : ℤ) - (k : ℤ)) = (j : ℤ) - (i : ℤ) by ring] at h

/-- Conversely, a polynomial in the degree-`d` piece of the integer-extended grading of `Proj`
lies in the degree-`d` piece of
`Stacks.AlgebraicGeometry.ProjectiveGenerator.homogeneousPiece`. -/
public theorem mem_homogeneousPiece_of_mem_integerGrading {d : ℤ}
    {p : MvPolynomial (Fin (n + 1)) A} (hp : p ∈ integerGrading (polyGrading A n) d) :
    p ∈ homogeneousPiece A n d := (mem_homogeneousPiece_iff_mem_integerGrading A n).2 hp

/-- The `(i, j)` entry of a matrix of the algebra, as an element of the degree-`(j - i)` piece
of the integer-extended grading. -/
public def matrixEntry (M : endomorphismMatrices A n) (i j : Fin (n + 1)) :
    integerGrading (polyGrading A n) ((j : ℤ) - (i : ℤ)) :=
  ⟨(M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) A)) i j,
    mem_integerGrading_of_mem_homogeneousPiece A n (M.2 i j)⟩

/-- **The morphism `𝒪_X(-j) ⟶ 𝒪_X(-i)` attached to the `(i, j)` entry** of a matrix of the
algebra: multiplication by that entry, which is homogeneous of degree `j - i`. -/
public def matrixEntryHom (M : endomorphismMatrices A n) (i j : Fin (n + 1)) :
    twistFamily A n j ⟶ twistFamily A n i :=
  twistMulHom (polyGrading A n) ((j : ℤ) - (i : ℤ)) (-(j : ℤ)) (-(i : ℤ)) (by ring)
    (matrixEntry A n M i j)

/-- Two endomorphisms of a finite biproduct with the same components are equal. -/
private theorem biproduct_matrix_ext {C : Type*} [Category C] [Preadditive C]
    [Limits.HasFiniteBiproducts C] {J : Type} [Finite J] {f : J → C} (φ ψ : ⨁ f ⟶ ⨁ f)
    (h : ∀ j i, biproduct.ι f j ≫ φ ≫ biproduct.π f i =
      biproduct.ι f j ≫ ψ ≫ biproduct.π f i) : φ = ψ :=
  biproduct.matrixEquiv.injective (funext fun j => funext fun i => h j i)

/-- The components of a sum of endomorphisms of a finite biproduct are the sums of the
components. Stated in an abstract preadditive category: at the concrete one the unifier does
not reach the identification of the ring addition of `CategoryTheory.End` with the addition of
the Hom group inside the heartbeat budget. -/
private theorem components_add {C : Type*} [Category C] [Preadditive C]
    [Limits.HasFiniteBiproducts C] {J : Type} [Finite J] {f : J → C} (φ ψ : End (⨁ f))
    (j i : J) :
    biproduct.ι f j ≫ (φ + ψ) ≫ biproduct.π f i =
      biproduct.ι f j ≫ φ ≫ biproduct.π f i + biproduct.ι f j ≫ ψ ≫ biproduct.π f i := by
  rw [Preadditive.add_comp, Preadditive.comp_add]

/-- The entry morphisms are additive in the matrix. -/
private theorem matrixEntryHom_add (M N : endomorphismMatrices A n) (i j : Fin (n + 1)) :
    matrixEntryHom A n (M + N) i j = matrixEntryHom A n M i j + matrixEntryHom A n N i j := by
  have hentry : matrixEntry A n (M + N) i j =
      matrixEntry A n M i j + matrixEntry A n N i j :=
    Subtype.ext (Matrix.add_apply _ _ i j)
  rw [matrixEntryHom, matrixEntryHom, matrixEntryHom, hentry]
  exact AddMonoidHom.map_add _ _ _

/-- The underlying function of the comparison map: the matrix of multiplications. -/
public def matrixToEndFun (M : endomorphismMatrices A n) : End (projTwistSum A n) :=
  biproduct.matrix fun j i => matrixEntryHom A n M i j

/-- **The `(i, j)` component of the endomorphism attached to a matrix is multiplication by its
`(i, j)` entry.** -/
@[simp] public theorem components_matrixToEndFun (M : endomorphismMatrices A n)
    (j i : Fin (n + 1)) :
    biproduct.ι (twistFamily A n) j ≫ matrixToEndFun A n M ≫
        biproduct.π (twistFamily A n) i = matrixEntryHom A n M i j := by
  rw [← Category.assoc, matrixToEndFun, biproduct.ι_matrix, biproduct.lift_π]

/-- The entry of a product of two matrices of the algebra, as an element of the degree-`(j - i)`
piece: the sum over `k` of the products of entries. -/
private theorem matrixEntry_mul (M N : endomorphismMatrices A n) (i j : Fin (n + 1)) :
    matrixEntry A n (M * N) i j =
      ∑ k : Fin (n + 1), (⟨(M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial
        (Fin (n + 1)) A)) i k * (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial
        (Fin (n + 1)) A)) k j, entry_mul_mem A n M N i j k⟩ :
          integerGrading (polyGrading A n) ((j : ℤ) - (i : ℤ))) := by
  refine Subtype.ext ?_
  rw [AddSubmonoid.coe_finset_sum]
  exact Matrix.mul_apply

/-- **The comparison map of [Stacks, Tag 0CS9]**: the upper triangular matrix algebra `R` acts
on the twist sum `P` by multiplication entry by entry, and that action is a ring homomorphism
`R ⟶ End(P)`. -/
public def matrixToEnd : endomorphismMatrices A n →+* End (projTwistSum A n) where
  toFun := matrixToEndFun A n
  map_one' := by
    refine biproduct_matrix_ext _ _ fun j i => ?_
    rw [components_matrixToEndFun, End.one_def, Category.id_comp, biproduct.ι_π]
    rcases eq_or_ne j i with rfl | hji
    · rw [dif_pos rfl, eqToHom_refl, matrixEntryHom, twistMulHom_apply]
      exact (twistMul_congr (polyGrading A n) _ (one_mem_integerGrading (polyGrading A n))
        (by ring) (zero_add _) (Matrix.one_apply_eq j)).trans
        (twistMul_one (polyGrading A n) (-(j : ℤ)) (one_mem_integerGrading (polyGrading A n)))
    · rw [dif_neg hji, matrixEntryHom, twistMulHom_apply]
      exact (twistMul_congr (polyGrading A n) _ (zero_mem
        (integerGrading (polyGrading A n) ((j : ℤ) - (i : ℤ)))) (by ring) (by ring)
        (Matrix.one_apply_ne (Ne.symm hji))).trans (twistMul_zero (polyGrading A n) _ _ _ (by ring))
  map_mul' M N := by
    refine biproduct_matrix_ext _ _ fun j i => ?_
    rw [components_matrixToEndFun, End.mul_def, ← Category.assoc,
      Stacks.AlgebraicGeometry.ProjKoszulComplex.biproduct_ι_comp_comp_π
        (twistFamily A n) (twistFamily A n) (twistFamily A n)
        (matrixToEndFun A n N) (matrixToEndFun A n M) j i]
    simp only [components_matrixToEndFun]
    rw [matrixEntryHom, matrixEntry_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [matrixEntryHom, matrixEntryHom, twistMulHom_apply, twistMulHom_apply,
      twistMulHom_apply, twistMul_comp]
    exact twistMul_congr (polyGrading A n) _ _ (by ring) (by ring) rfl
  map_zero' := by
    refine biproduct_matrix_ext _ _ fun j i => ?_
    rw [components_matrixToEndFun, zero_comp, comp_zero, matrixEntryHom]
    exact (twistMulHom (polyGrading A n) _ _ _ (by ring)).map_zero
  map_add' M N := by
    refine biproduct_matrix_ext _ _ fun j i => ?_
    rw [components_matrixToEndFun, components_add, components_matrixToEndFun,
      components_matrixToEndFun]
    exact matrixEntryHom_add A n M N i j

/-- The comparison map on a matrix, read off entry by entry. -/
public theorem components_matrixToEnd (M : endomorphismMatrices A n) (j i : Fin (n + 1)) :
    biproduct.ι (twistFamily A n) j ≫ matrixToEnd A n M ≫
        biproduct.π (twistFamily A n) i = matrixEntryHom A n M i j :=
  components_matrixToEndFun A n M j i

end Matrices

end Stacks.AlgebraicGeometry.ProjectiveGenerator

end
