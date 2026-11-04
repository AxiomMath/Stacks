module

public import Mathlib.CategoryTheory.Idempotents.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.MonoidalStructure
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.ProjectiveLineAlgebra
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksCore.Tactic.StacksAttribute

/-!
# The motive of the projective line, and the Lefschetz motive

Let `X = P¹_k` and let `x ∈ X` be a `k`-rational point. Example 0FG6 attaches to `x` the two
fibre classes `c₀ = [x × X]` and `c₂ = [X × x]` of `Corr⁰(X, X)`; they are orthogonal idempotents
with `[Δ] = c₀ + c₂`. The motive `(X, c₂, 0)` is the *Lefschetz motive*, written `L`, `𝐋`,
`Q(-1)` or `h²(P¹_k)` in the literature, and Lemma 0FGD identifies the two summands it and `c₀`
cut out of `h(X)`, namely `(X, c₀, 0) ≅ 1` and `(X, c₂, 0) ≅ 1(-1)`. Consequently

  `h(P¹_k) ≅ 1 ⊕ 1(-1)` in `M_k`,

which is Lemma 0FGG, and the Lefschetz motive is invertible (Categories, Definition 0FFN) with
inverse `1(1)`, the *Tate motive*.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceStructure.lefschetzMotive`: **Stacks 0FGE**, the Lefschetz
  motive `L = (X, c₂, 0)`.
* `CategoryTheory.Idempotents.Karoubi.orthogonalBinaryBicone` and
  `CategoryTheory.Idempotents.Karoubi.orthogonalBinaryBiproductData`: a pair of orthogonal
  idempotents summing to the identity of `X` exhibits the image of `X` in the Karoubi envelope as
  the direct sum of the two formal direct factors they cut out.
* `Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineBiproductData`: **Stacks 0FGG**,
  the bilimit bicone with point `h(P¹_k)` and summands `1` and `1(-1)`.
* `Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineMotiveIso`: **Stacks 0FGG**, the
  isomorphism `h(P¹_k) ≅ 1 ⊕ 1(-1)`.

## Main results

* `Stacks.WeilCohomology.CorrespondenceStructure.lefschetzProjector_idem`,
  `...comp_lefschetzProjector` and `...lefschetzProjector_comp`: the composition rules
  `c₂ ∘ c₂ = c₂`, `c₀ ∘ c₂ = 0` and `c₂ ∘ c₀ = 0` of Example 0FG6, for endomorphisms of an
  object of the category of correspondences.
* `CategoryTheory.Idempotents.Karoubi.orthogonalBinaryBiconeIsBilimit`: that bicone is a bilimit.
* `Stacks.WeilCohomology.CorrespondenceStructure.hasBinaryBiproduct_motive`: the direct sum
  `1 ⊕ 1(-1)` exists in `M_k`.
* `Stacks.WeilCohomology.CorrespondenceStructure.lefschetzMotiveHasInverse`: **Stacks 0FGE**, the
  Lefschetz motive is invertible, with inverse the Tate motive `1(1)`.

## Implementation notes

**Where the statement lives, and where the Tate twist lives.** As in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.MonoidalStructure`, the ambient
category `D` is the opposite of the smooth projective schemes over `k` enlarged by the Tate
twists, so that an object of `D` is a pair `(X, m)` and a correspondence
`S.Hom (X, m) (Y, n)` is an element of `Corr^{n - m}(X, Y)`. The category `M_k` of Chow motives
is the Karoubi envelope of the category of correspondences (Stacks 0FGA), so a motive
`(X, p, m)` is the formal direct factor `⟨Obj.mk X, p⟩ : Karoubi S.Obj` and the unit motive
`1 = (Spec k, 1, 0)` is `(toKaroubi S.Obj).obj (Obj.mk P)` for `P` the monoidal unit of `D`,
which is `Spec k` by `Stacks.WeilCohomology.CorrespondenceStructure.tensorUnit_as`. Likewise
`1(-1) = (Spec k, 1, -1)` is the image of the object `T = (Spec k, -1)` of `D`. No motive, no
category of motives and no Tate twist is redefined here: `(toKaroubi S.Obj).obj` is by definition
the functor `h` of Stacks 0FGA, `h` being the graph functor followed by the canonical embedding
and the graph functor being the identity on objects.

**The direct sum.** `M_k` is `ℚ`-linear (Stacks 0FGA), and the `ℚ`-linear — indeed already the
preadditive — structure of the correspondence spaces is the content of Stacks 0FG2, carried by
`Stacks.WeilCohomology.GradedCompositionData`; it enters below as the instance hypothesis
`[Preadditive S.Obj]`, exactly as it does for the `ℚ`-linear structure of `M_k` itself. Given it,
`Karoubi S.Obj` is preadditive, so `1 ⊕ 1(-1)` means the binary biproduct. What Stacks 0FGG adds
to Stacks 0FGD is proved here in the form that does not presuppose that biproduct to exist:
`Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineBiproductData` produces a binary
bicone over `1` and `1(-1)` whose point is `h(P¹_k)` together with a proof that it is a bilimit,
which is what "`h(P¹_k)` is the direct sum of `1` and `1(-1)`" asserts. The existence of
`1 ⊕ 1(-1)` follows (`...hasBinaryBiproduct_motive`), and
`Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineMotiveIso` then states the source's
isomorphism `h(P¹_k) ≅ 1 ⊞ 1(-1)` in the `⊞` notation; its `HasBinaryBiproduct` instance
argument is the one discharged by `...hasBinaryBiproduct_motive` from the very same hypotheses,
and is present only because the `⊞` notation cannot be written without it.

**The carried hypotheses, and why each is upstream.** Three inputs are carried, and none of them
is the conclusion of Stacks 0FGG:

* `hsum : c₀ + c₂ = 𝟙 X` and `h₀ : c₀ ∘ c₀ = c₀`, the two irreducible assertions of
  Example 0FG6. They are intersection computations on `P¹ × P¹` — "a computation shows" in the
  source — and composition of correspondences, which needs the intersection product of Stacks
  0FC1, the Gysin pullback of Stacks 0FFB and the projection formula of Stacks 0FFC, is not
  formalized in this repository. The remaining three rules of Example 0FG6 are *not* carried:
  `...lefschetzProjector_idem`, `...comp_lefschetzProjector` and `...lefschetzProjector_comp`
  derive them from these two, by
  `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.ProjectiveLineAlgebra` applied to
  the endomorphism ring of the object.
* `e₀ : (X, c₀, 0) ≅ 1` and `e₂ : (X, c₂, 0) ≅ 1(-1)`, the two conclusions of Lemma 0FGD. The
  source's proof of Lemma 0FGG is "this follows from Example 0FG6 and Lemma 0FGD", so these are
  precisely its other input, and they are proved — part (1) outright, part (2) from the source's
  two composition formulas — by
  `StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ProjectiveLineSummands`, whose
  `constantGraphMotiveIso` and `tateProjectorMotiveIso` instantiate them. That module is not
  imported here because it is absent from this working tree, so this file is routed through
  modules that `Stacks.WeilCohomology.CorrespondenceStructure` and the Karoubi envelope supply
  directly; no statement is weakened by the routing, only the two isomorphisms are received as
  arguments rather than built on the spot.

What is proved is therefore exactly the step from Example 0FG6 and Lemma 0FGD to Lemma 0FGG: that
two orthogonal idempotents summing to `[Δ]` split `h(X) = (X, [Δ], 0)` as a direct sum of the two
motives they cut out. That step is isolated, with no mention of correspondences, as
`CategoryTheory.Idempotents.Karoubi.orthogonalBinaryBiproductData`.

**The invertibility of the Lefschetz motive.** The symmetric monoidal structure of `M_k` is
Stacks 0FGC and is not constructed in this repository — the monoidal structure carried by
`Stacks.WeilCohomology.CorrespondenceStructure` is that of the category of correspondences,
Stacks 0FG7, not of its Karoubi envelope — so it enters
`Stacks.WeilCohomology.CorrespondenceStructure.lefschetzMotiveHasInverse` as an instance
hypothesis, and a two-sided tensor inverse of `1(-1)` as an argument. What that declaration
proves is the remark's own inference: the Lefschetz motive is isomorphic to `1(-1)` by
Lemma 0FGD, hence invertible, and `...lefschetzMotiveHasInverse_inv` records that the inverse
object produced is the one given, that is the Tate motive `1(1)`. The Tate motive itself gets no
definition of its own: `1(1)` is the image of the object `(Spec k, 1)` of `D`, and the Tate twist
operation on `D` is not carried here, so naming it would name nothing.

**Abstraction over the geometry.** As throughout
`StacksDraft.AlgebraicGeometry.WeilCohomology.Correspondences`, neither smoothness, nor
projectivity, nor a base field, nor the projective line itself is imposed: the arguments use none
of them. Instantiating `D` by the opposite of the smooth projective schemes over `k` enlarged by
the Tate twists, `Q` by `P¹_k`, `P` by `Spec k` and `T` by `(Spec k, -1)`, and `c₀`, `c₂` by the
two fibre classes of a rational point recovers the statements of the source verbatim.

## References

* [Stacks Project, Tag 0FGG](https://stacks.math.columbia.edu/tag/0FGG)
* [Stacks Project, Tag 0FGE](https://stacks.math.columbia.edu/tag/0FGE)
* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe v u w

namespace CategoryTheory.Idempotents.Karoubi

/-! ### Splitting an object along a pair of orthogonal idempotents -/

section OrthogonalIdempotents

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The binary bicone over the two formal direct factors of `X` cut out by orthogonal idempotents
`p` and `q`, with the image `(toKaroubi C).obj X` of `X` as its point: the two injections and the
two projections are all given by `p`, resp. `q`, itself, as in
`CategoryTheory.Idempotents.Karoubi.decompId`. -/
@[simps]
def orthogonalBinaryBicone {X : C} {p q : X ⟶ X} (hp : p ≫ p = p) (hq : q ≫ q = q)
    (hpq : p ≫ q = 0) (hqp : q ≫ p = 0) :
    BinaryBicone (⟨X, p, hp⟩ : Karoubi C) ⟨X, q, hq⟩ where
  pt := (toKaroubi C).obj X
  fst := Karoubi.decompId_p (⟨X, p, hp⟩ : Karoubi C)
  snd := Karoubi.decompId_p (⟨X, q, hq⟩ : Karoubi C)
  inl := Karoubi.decompId_i (⟨X, p, hp⟩ : Karoubi C)
  inr := Karoubi.decompId_i (⟨X, q, hq⟩ : Karoubi C)
  inl_fst := (Karoubi.decompId _).symm
  inl_snd := Karoubi.hom_eq_zero_iff.2 hpq
  inr_fst := Karoubi.hom_eq_zero_iff.2 hqp
  inr_snd := (Karoubi.decompId _).symm

/-- If the two orthogonal idempotents sum to the identity of `X`, the bicone of
`CategoryTheory.Idempotents.Karoubi.orthogonalBinaryBicone` is a bilimit: its total endomorphism
`p ∘ p + q ∘ q = p + q` is the identity, which in a preadditive category is exactly what makes a
binary bicone a limit cone and a colimit cocone. -/
def orthogonalBinaryBiconeIsBilimit {X : C} {p q : X ⟶ X} (hp : p ≫ p = p) (hq : q ≫ q = q)
    (hpq : p ≫ q = 0) (hqp : q ≫ p = 0) (hsum : p + q = 𝟙 X) :
    (orthogonalBinaryBicone hp hq hpq hqp).IsBilimit :=
  isBinaryBilimitOfTotal _ (by
    ext
    change p ≫ p + q ≫ q = 𝟙 X
    rw [hp, hq, hsum])

/-- A pair of orthogonal idempotents summing to the identity of `X` exhibits the image of `X` in
the Karoubi envelope as the direct sum of the two formal direct factors they cut out:
`(toKaroubi C).obj X` is a binary biproduct of `⟨X, p⟩` and `⟨X, q⟩`. -/
def orthogonalBinaryBiproductData {X : C} {p q : X ⟶ X} (hp : p ≫ p = p) (hq : q ≫ q = q)
    (hpq : p ≫ q = 0) (hqp : q ≫ p = 0) (hsum : p + q = 𝟙 X) :
    BinaryBiproductData (⟨X, p, hp⟩ : Karoubi C) ⟨X, q, hq⟩ where
  bicone := orthogonalBinaryBicone hp hq hpq hqp
  isBilimit := orthogonalBinaryBiconeIsBilimit hp hq hpq hqp hsum

end OrthogonalIdempotents

end CategoryTheory.Idempotents.Karoubi

namespace Stacks.WeilCohomology

namespace CorrespondenceStructure

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
  (S : CorrespondenceStructure.{v, u, w} D) [Preadditive S.Obj]
  {Q : D} (c₀ c₂ : (Obj.mk Q : S.Obj) ⟶ Obj.mk Q)

/-! ### The two projectors of Example 0FG6 -/

/-- **Stacks Project, Tag 0FG6.** The composition rule `c₂ ∘ c₂ = c₂`, for endomorphisms of an
object of the category of correspondences: the complement of an idempotent is idempotent. This is
`Stacks.WeilCohomology.mul_self_of_add_eq_one` at the endomorphism ring of the object. -/
theorem lefschetzProjector_idem (hsum : c₀ + c₂ = 𝟙 (Obj.mk Q : S.Obj))
    (h₀ : c₀ ≫ c₀ = c₀) : c₂ ≫ c₂ = c₂ :=
  mul_self_of_add_eq_one (A := End (Obj.mk Q : S.Obj)) hsum h₀

/-- **Stacks Project, Tag 0FG6.** The composition rule `c₀ ∘ c₂ = 0`, for endomorphisms of an
object of the category of correspondences: an idempotent and its complement are orthogonal. This
is `Stacks.WeilCohomology.mul_eq_zero_of_add_eq_one'` at the endomorphism ring of the object, the
product of the endomorphism ring being composition in the other order. -/
theorem comp_lefschetzProjector (hsum : c₀ + c₂ = 𝟙 (Obj.mk Q : S.Obj))
    (h₀ : c₀ ≫ c₀ = c₀) : c₀ ≫ c₂ = 0 :=
  mul_eq_zero_of_add_eq_one' (A := End (Obj.mk Q : S.Obj)) hsum h₀

/-- **Stacks Project, Tag 0FG6.** The composition rule `c₂ ∘ c₀ = 0`, for endomorphisms of an
object of the category of correspondences. This is
`Stacks.WeilCohomology.mul_eq_zero_of_add_eq_one` at the endomorphism ring of the object. -/
theorem lefschetzProjector_comp (hsum : c₀ + c₂ = 𝟙 (Obj.mk Q : S.Obj))
    (h₀ : c₀ ≫ c₀ = c₀) : c₂ ≫ c₀ = 0 :=
  mul_eq_zero_of_add_eq_one (A := End (Obj.mk Q : S.Obj)) hsum h₀

/-! ### The Lefschetz motive -/

/-- **Stacks Project, Tag 0FGE.** The *Lefschetz motive* `(X, c₂, 0)`: the formal direct factor
of `X` cut out by the projector `c₂ = [X × x]` of Example 0FG6, with no Tate twist. In the
literature it is denoted `L`, `𝐋`, `Q(-1)` or `h²(P¹_k)`.

For the source `X` is `P¹_k` and `c₂` is the class of the fibre `X × x` of a `k`-rational point
`x`, whose idempotence is the composition rule `c₂ ∘ c₂ = c₂` of Example 0FG6 — available as
`Stacks.WeilCohomology.CorrespondenceStructure.lefschetzProjector_idem` once `[Δ] = c₀ + c₂` and
`c₀ ∘ c₀ = c₀` are known — and without which `(X, c₂, 0)` is not a motive at all. -/
@[stacks 0FGE "the Lefschetz motive (X, c_2, 0), written L, bold L, Q(-1) or h^2(P^1_k)"]
def lefschetzMotive (hc₂ : c₂ ≫ c₂ = c₂) : Karoubi S.Obj :=
  ⟨Obj.mk Q, c₂, hc₂⟩

omit [Preadditive S.Obj] in
@[simp]
theorem lefschetzMotive_X (hc₂ : c₂ ≫ c₂ = c₂) : (S.lefschetzMotive c₂ hc₂).X = Obj.mk Q :=
  rfl

omit [Preadditive S.Obj] in
@[simp]
theorem lefschetzMotive_p (hc₂ : c₂ ≫ c₂ = c₂) : (S.lefschetzMotive c₂ hc₂).p = c₂ :=
  rfl

/-! ### The decomposition of the motive of the projective line -/

variable {P T : D}

/-- **Stacks Project, Tag 0FGG.** In `M_k` the motive `h(P¹_k)` is the direct sum of `1` and
`1(-1)`: the binary bicone over `1` and `1(-1)` with point `h(P¹_k)`, together with the proof
that it is a bilimit.

The hypotheses `hsum` and `h₀` are the two irreducible assertions `[Δ] = c₀ + c₂` and
`c₀ ∘ c₀ = c₀` of Example 0FG6; the other two composition rules it states are derived. The
isomorphisms `e₀` and `e₂` are the two conclusions `(X, c₀, 0) ≅ 1` and `(X, c₂, 0) ≅ 1(-1)` of
Lemma 0FGD, `1` being the image of the monoidal unit `P = Spec k` of the ambient category and
`1(-1)` the image of its Tate twist `T = (Spec k, -1)`; the source's proof of Lemma 0FGG is
precisely the deduction from these. What is proved is that deduction: the two projectors being
orthogonal idempotents with sum `[Δ]`, the motive `h(P¹_k) = (P¹_k, [Δ], 0)` splits as the direct
sum of the two summands they cut out, which `e₀` and `e₂` then name. -/
@[stacks 0FGG "h(P^1_k) is the direct sum of 1 and 1(-1): the bilimit bicone with point h(P^1_k);
granted: Example 0FG6's [Delta] = c_0 + c_2 and c_0 o c_0 = c_0, and the two isomorphisms of
Lemma 0FGD"]
def projectiveLineBiproductData (hsum : c₀ + c₂ = 𝟙 (Obj.mk Q : S.Obj)) (h₀ : c₀ ≫ c₀ = c₀)
    (e₀ : (⟨Obj.mk Q, c₀, h₀⟩ : Karoubi S.Obj) ≅ (toKaroubi S.Obj).obj (Obj.mk P))
    (e₂ : S.lefschetzMotive c₂ (S.lefschetzProjector_idem c₀ c₂ hsum h₀) ≅
      (toKaroubi S.Obj).obj (Obj.mk T)) :
    BinaryBiproductData ((toKaroubi S.Obj).obj (Obj.mk P)) ((toKaroubi S.Obj).obj (Obj.mk T)) :=
  (Karoubi.orthogonalBinaryBiproductData h₀ (S.lefschetzProjector_idem c₀ c₂ hsum h₀)
      (S.comp_lefschetzProjector c₀ c₂ hsum h₀) (S.lefschetzProjector_comp c₀ c₂ hsum h₀)
      hsum).ofIso e₀ e₂

/-- The direct sum `1 ⊕ 1(-1)` exists in `M_k`: the bicone of
`Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineBiproductData` is one. This
discharges the instance argument of
`Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineMotiveIso` from the same
hypotheses. -/
theorem hasBinaryBiproduct_motive (hsum : c₀ + c₂ = 𝟙 (Obj.mk Q : S.Obj)) (h₀ : c₀ ≫ c₀ = c₀)
    (e₀ : (⟨Obj.mk Q, c₀, h₀⟩ : Karoubi S.Obj) ≅ (toKaroubi S.Obj).obj (Obj.mk P))
    (e₂ : S.lefschetzMotive c₂ (S.lefschetzProjector_idem c₀ c₂ hsum h₀) ≅
      (toKaroubi S.Obj).obj (Obj.mk T)) :
    HasBinaryBiproduct ((toKaroubi S.Obj).obj (Obj.mk P))
      ((toKaroubi S.Obj).obj (Obj.mk T)) :=
  .mk (S.projectiveLineBiproductData c₀ c₂ hsum h₀ e₀ e₂)

/-- **Stacks Project, Tag 0FGG.** In `M_k` we have `h(P¹_k) ≅ 1 ⊕ 1(-1)`.

This is the isomorphism form of
`Stacks.WeilCohomology.CorrespondenceStructure.projectiveLineBiproductData`, with the direct sum
written in the `⊞` notation; the `HasBinaryBiproduct` instance argument that notation needs is
discharged, from the same hypotheses, by
`Stacks.WeilCohomology.CorrespondenceStructure.hasBinaryBiproduct_motive`. -/
@[stacks 0FGG "in M_k we have h(P^1_k) iso 1 + 1(-1); granted: Example 0FG6's [Delta] = c_0 + c_2
and c_0 o c_0 = c_0, and the two isomorphisms of Lemma 0FGD"]
noncomputable def projectiveLineMotiveIso
    (hsum : c₀ + c₂ = 𝟙 (Obj.mk Q : S.Obj)) (h₀ : c₀ ≫ c₀ = c₀)
    (e₀ : (⟨Obj.mk Q, c₀, h₀⟩ : Karoubi S.Obj) ≅ (toKaroubi S.Obj).obj (Obj.mk P))
    (e₂ : S.lefschetzMotive c₂ (S.lefschetzProjector_idem c₀ c₂ hsum h₀) ≅
      (toKaroubi S.Obj).obj (Obj.mk T))
    [HasBinaryBiproduct ((toKaroubi S.Obj).obj (Obj.mk P))
      ((toKaroubi S.Obj).obj (Obj.mk T))] :
    (toKaroubi S.Obj).obj (Obj.mk Q) ≅
      (toKaroubi S.Obj).obj (Obj.mk P) ⊞ (toKaroubi S.Obj).obj (Obj.mk T) :=
  biprod.uniqueUpToIso _ _ (S.projectiveLineBiproductData c₀ c₂ hsum h₀ e₀ e₂).isBilimit

/-! ### Invertibility of the Lefschetz motive -/

/-- **Stacks Project, Tag 0FGE.** The Lefschetz motive is invertible, with inverse the Tate
motive `1(1)`.

By Lemma 0FGD the Lefschetz motive is isomorphic to `1(-1)`, which is the hypothesis `e`; a
two-sided tensor inverse of `1(-1)` — its inverse object being `1(1)`, the Tate motive — is the
hypothesis `h`, and the symmetric monoidal structure of `M_k`, which is Stacks 0FGC and is not
constructed in this repository, is the instance hypothesis. The inverse object produced is the
one given, as recorded by
`Stacks.WeilCohomology.CorrespondenceStructure.lefschetzMotiveHasInverse_inv`. -/
@[stacks 0FGE "the Lefschetz motive is invertible with inverse the Tate motive 1(1); granted:
the monoidal structure on M_k (Stacks 0FGC), the isomorphism L iso 1(-1) of Lemma 0FGD, and a
two-sided tensor inverse of 1(-1)"]
def lefschetzMotiveHasInverse [MonoidalCategory (Karoubi S.Obj)] (hc₂ : c₂ ≫ c₂ = c₂)
    {N : Karoubi S.Obj} (e : S.lefschetzMotive c₂ hc₂ ≅ N) (h : HasInverse N) :
    HasInverse (S.lefschetzMotive c₂ hc₂) where
  inv := h.inv
  isoLeft := tensorIso e (Iso.refl h.inv) ≪≫ h.isoLeft
  isoRight := tensorIso (Iso.refl h.inv) e ≪≫ h.isoRight

omit [Preadditive S.Obj] in
@[simp]
theorem lefschetzMotiveHasInverse_inv [MonoidalCategory (Karoubi S.Obj)] (hc₂ : c₂ ≫ c₂ = c₂)
    {N : Karoubi S.Obj} (e : S.lefschetzMotive c₂ hc₂ ≅ N) (h : HasInverse N) :
    (S.lefschetzMotiveHasInverse c₂ hc₂ e h).inv = h.inv :=
  rfl

end CorrespondenceStructure

end Stacks.WeilCohomology

end
