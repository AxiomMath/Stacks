module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple

/-!
# Pulling back the integral tensor powers of an invertible module

Let `k : T' ⟶ T` be a morphism of schemes and `L` an invertible `𝒪_T`-module. This file
constructs the comparison

`k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}`

for an **integral** exponent `n`, between the tensor powers of Tag 01CU, in the spelling the
Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of Section 01NS is graded by.

## Why this is here

Section 01NS attaches to each `d ≥ 1` the functor `F_d` whose value on a test scheme `T` is the
set of strict equivalence classes of quadruples `(d, f : T → S, L, ψ)`, and Tag 01NU asserts
that for an affine base `F_d` is representable by the open `U_d ⊆ Proj Γ(S, 𝒜)`. Representability
is a statement about a *functor*, and making `F_d` one needs the pullback of a quadruple along a
morphism `k : T' ⟶ T` of test schemes, which in turn needs the components
`ψ_i : f^*𝒜_{id} ⟶ L^{⊗ i}` to be carried into `(k^*L)^{⊗ i}` — exactly the comparison above,
in **every** integral degree.

**`F_d` is a functor in this repository**: it is
`StacksDraft.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor.Fd.functor`, with both functor
laws proved, built on `...RelativeProjQcohSheaf.UnionPullback.Fd.pullback`. Older notes in this
directory that call `F_d` a family of sets rather than a functor describe the state of the
import chain at the point where they stand, not the state of the repository; the ones that said
otherwise have been corrected. What that construction actually consumes is
`...RelativeProjQcohSheaf.TwistingPullback.laurentPullback` — a **second** construction of the
same comparison, as `Stacks.TensorPowerPullback.pullbackIntPowIso` — so `pieceIso` below and its
multiplicativity are at present a parallel development of it and have no consumer. Which of the
two survives is a question for a deduplication pass, not for a reader of this file.

## The construction, and why it is not an induction

The nonnegative half is the usual recursion: `L^{⊗ (n+1)} = L^{⊗ n} ⊗ L`, the pullback
distributes over the tensor product by Tag 01CD, and the comparison at `n` is applied in the
first factor. The negative half admits no such recursion — the negative tensor powers of Tag
01CU are iterates of a *chosen* quasi-inverse of right tensoring by `L`, which `k^*` has no
reason to commute with — and is instead obtained by **cancellation**: tensoring on the right by
`k^*L` is an equivalence, hence fully faithful, so an isomorphism between the two sides tensored
by `k^*L` is the image of a unique isomorphism between the two sides, and the two sides tensored
by `k^*L` are exactly the two sides of the comparison at `n + 1`.

## Multiplicativity, in every bidegree

The comparison is **compatible with the multiplication of the Laurent algebra in every integral
bidegree** (`pieceIso_mul`): for all `n m : ℤ` the square

    k^*(L^{⊗ n} ⊗ L^{⊗ m}) ──k^*μ──> k^*(L^{⊗ (n+m)})
            │                              │
       01CD, then the two comparisons        │ the comparison in degree n+m
            v                                v
    (k^*L)^{⊗ n} ⊗ (k^*L)^{⊗ m} ──μ──> (k^*L)^{⊗ (n+m)}

commutes, where `μ` is the coherent multiplication
`Stacks.SheafOfModules.TensorPower.coherentMulIso` of Tag 01CU. This is the input the pullback of
a quadruple needs beyond the degreewise comparison itself.

The multiplication of Tag 01CU is *chosen*, independently upstairs and downstairs, so nothing
about it is available except its five coherence laws; the square is therefore proved by
induction on the second exponent out of bidegree `(n, 0)`, where the law is the right unitor.
Upwards the step is the associativity law at `k = 1` together with the bidegree-`(n, 1)` case,
which is exactly what the successor law `pieceIso_succ` says once `coherentMulIso_one_right` has
identified multiplication by the first power with the successor comparison. Downwards — and this
is what reaches the negative exponents — the same equation is read backwards: the associativity
law determines the bidegree-`(n, m)` multiplication only after tensoring on the right by
`L^{⊗ 1}`, and tensoring by an invertible module is faithful, so the square in bidegree `(n, m)`
follows from the square in bidegree `(n, m + 1)`. The pullback-side inputs are the three
coherences of Tag 01CD proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` — compatibility with the
associator and the two unitors, and naturality in each variable.

One bridge is needed to put the two halves in the same vocabulary. The coherence laws of Tag
01CU are stated against the structural isomorphisms
`Stacks.SheafOfModules.Invertible.tensorProduct…` of the tensor product sheaf, while the
coherences of Tag 01CD are stated against the structural morphisms `α_`, `λ_`, `ρ_`, `⊗ₘ`, `◁`,
`▷` of the monoidal structure of Tag 01CA. The `bridge_…` lemmas below identify the two, by
`Stacks.SheafOfModules.tensorProductAssociator_eq_comparison` and its siblings; they are the
same morphisms, named twice.

The recursion is run **as data**, by structural recursion on `ℤ` through its two constructors,
and not through `Int.induction_on`. That is what makes `pieceIso_succ` and `pieceIso_pred`
available: a comparison extracted from a `Nonempty` by `Classical.choice` satisfies no equation
at all, and so can never be shown compatible with anything downstream. (The repository already
contains such a comparison for the other spelling of the tensor powers,
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIntIso` in
`StacksFrontier/AlgebraicGeometry/TwistedSheaf/PushforwardTwist.lean`, defined as
`(nonempty_pullbackTensorPowerIntIso f L n).some`; nothing can be proved about it, and nothing
below uses it.)

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.pullbackModule` — the
  pullback `k^*L`, which is again invertible.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.PieceCmp` — the type of a
  comparison in a single degree, `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.succStep` and `predStep` —
  the two steps, raising and lowering the degree by one.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.pieceIso` — **the comparison
  `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` for every integer `n`**, as data.
* `...LaurentPullback.mulIso`, `reindexIso`, `succIso`, `oneIsoL` — the coherent
  multiplication, the reindexing, the successor comparison and the identification `L^{⊗ 1} = L`
  of Tag 01CU, with their types ascribed at the spelling of a scheme. Without the ascription a
  term mixing `Stacks.RingedSpace.structureRingSheaf` with
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is not type-correct at reducible
  transparency and no `rw` can operate on it.
* `...LaurentPullback.MulCompat` — the multiplicativity square in one bidegree.

## Main results

* `...LaurentPullback.succStep_predStep` and `predStep_succStep` — the two steps are mutually
  inverse. This is where the fully-faithfulness of right tensoring by `k^*L` is used.
* `...LaurentPullback.pieceIso_zero` — in degree `0` the comparison is the unit comparison
  `k^*𝒪_T ≅ 𝒪_{T'}` of Tag 01CD.
* `...LaurentPullback.pieceIso_succ` — **the successor law, in every integral degree**: the
  comparison at `n + 1` is the comparison at `n` pushed up by `succStep`. Stated for all
  `n : ℤ`, not only for `n ≥ 0`, this is what pins the family down: together with
  `pieceIso_zero` it determines `pieceIso` uniquely, since `succStep` is invertible.
* `...LaurentPullback.pieceIso_pred` — the same law read downwards.
* `...LaurentPullback.pieceIso_mul` — **the comparison is multiplicative in every integral
  bidegree**: it intertwines the coherent multiplication of Tag 01CU on `L` with the one on
  `k^*L`, for all `n m : ℤ`. This is the result the module exists for.
* `...LaurentPullback.mulCompat_zero` and `mulCompat_one` — the square in the bidegrees `(n, 0)`
  and `(n, 1)`, for every integer `n`.
* `...LaurentPullback.mulCompat_succ` and `mulCompat_of_succ` — the inductive step, upwards and
  downwards.
* `...LaurentPullback.pieceIso_reindex`, `pieceIso_reindex_inv`, `pieceIso_succIso`,
  `pieceIso_one` and `pieceIso_oneIso` — compatibility of the comparison with reindexing, with
  the successor comparison and with the identification `L^{⊗ 1} = L`, and its value in degree
  one.
* `...LaurentPullback.mulHom_laurent` and `mulSheaf_laurent` — the multiplication of the
  Laurent algebra as a morphism out of the tensor product sheaf, which is the spelling
  `...RelativeProjQcohSheaf.Twisting.app_mul` uses, **is** the coherent multiplication
  `coherentMulIso` of Tag 01CU, which is the spelling `pieceIso_mul` is stated for.
* `...LaurentPullback.monoidalStep` — the monoidal algebra of the inductive step, isolated in a
  bare monoidal category.
* `...LaurentPullback.bridge_leftUnitor`, `bridge_rightUnitor`, `bridge_associator`,
  `bridge_tensorIso` and `bridge_tensorRight` — the structural isomorphisms of the tensor
  product sheaf, against which Tag 01CU states its coherence laws, are the structural morphisms
  of the monoidal structure of Tag 01CA.

## Not done here

* **The pullback of a quadruple is not constructed here.** It is built in
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback`, against the other
  construction of the comparison; nothing below is used there.
  Multiplicativity, which was the missing input, is proved above, and so is the identification
  `mulSheaf_laurent` of `SheafOfModules.GradedAlgebra.mulSheaf (laurent L)` — the spelling of
  the multiplication that `...RelativeProjQcohSheaf.Twisting.app_mul` uses — with
  `coherentMulIso`. The composition comparison `(k ≫ f)^* ≅ k^* ∘ f^*` and its monoidality are
  available too, as `Stacks.PullbackTensorCoherence.pullbackCompIso` and
  `Stacks.PullbackTensorCoherence.isMonoidal_pullbackCompIso_hom`. What is left is the
  assembly: the pulled-back `Twisting`, the preservation of the surjectivity of its degree-one
  component, and — for the functoriality of `F_d` rather than for a single pullback — the
  compatibility of `pieceIso` with the composition of morphisms of test schemes and with the
  identity, each a further induction on the exponent of the same shape as `pieceIso_mul`. Those
  last two are now done, as `...RelativeProjQcohSheaf.LaurentComposition.pieceIso_comp` and
  `...RelativeProjQcohSheaf.LaurentIdentity.pieceIso_id`; the pulled-back `Twisting` is not.
* **Those last two laws have a prerequisite, and it is not the induction itself.** Neither can
  be *stated* without a degreewise comparison `M^{⊗ i} ≅ M'^{⊗ i}` induced by an isomorphism
  `M ≅ M'` of invertible modules: the two sides of each law carry merely isomorphic modules —
  `k'^*k^*L` against `(k' ≫ k)^*L` for composition, `(𝟙_T)^*L` against `L` for the identity —
  and a strict equivalence of quadruples of Section 01NS is an isomorphism of the invertible
  modules carrying one `ψ` to the other in **every** integral degree. That comparison, with its
  successor law and its multiplicativity, is
  `StacksDraft.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso` and
  `...LaurentCongr.congrIso_mul`; `Stacks.SheafOfModules.TensorPower.tensorPowerCongr` cannot
  serve, for the reason that module's docstring records.
* Consequently **Tag 01NU is not proved in this file**: neither the representability of `F_d` by
  `U_d` over an affine base, nor the identification of `F_d` with the functor of triples of
  Section 01N4 that the source's proof goes through. Both are proved elsewhere in this
  directory — the identification by `...RelativeProjQcohSheaf.veroneseSections` together with
  `...AffineTripleSections.fdOfHom` and the two round trips
  `...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_fdOfHom` and
  `...RelativeProjQcohSheaf.Quadruple.fdOfHom_classifyingHomOfClass`, assembled as
  `...RelativeProjQcohSheaf.Quadruple.fdEquiv`, and the representability as
  `...RelativeProjQcohSheaf.Fd.representableByDegreeOpen` of
  `StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineFdRepresentable.lean`.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe v u w

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-! ### The structural isomorphisms of the tensor product sheaf are the monoidal ones -/

section Bridge

open Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- The left unit constraint of the tensor product sheaf, against which Tag 01CU states its
unit law, is the left unitor of the monoidal structure of Tag 01CA. -/
theorem bridge_leftUnitor (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductLeftUnitor O hO M).hom = (λ_ M).hom := by
  rw [tensorProductLeftUnitor_eq_comparison]
  exact Strict.leftUnitor_hom_aux O hO M

/-- The right unit constraint of the tensor product sheaf is the right unitor of the monoidal
structure of Tag 01CA. -/
theorem bridge_rightUnitor (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductRightUnitor O hO M).hom = (ρ_ M).hom := by
  rw [tensorProductRightUnitor_eq_comparison]
  exact Strict.rightUnitor_hom_aux O hO M

/-- The associativity constraint of the tensor product sheaf is the associator of the monoidal
structure of Tag 01CA. -/
theorem bridge_associator
    (M N P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductAssociator O hO M N P).hom = (α_ M N P).hom :=
  tensorProductAssociator_eq_comparison O hO M N P

/-- The tensor product sheaf of two isomorphisms is their monoidal tensor product. -/
theorem bridge_tensorIso
    {M M' N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (a : M ≅ M') (b : N ≅ N') :
    (Invertible.tensorProductIso O hO a b).hom = a.hom ⊗ₘ b.hom :=
  sheafifyTensorHom_eq_comparison O hO a.hom b.hom

/-- `bridge_tensorIso` with the first factor an identity: a left whiskering. -/
theorem bridge_tensorIso_left
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (b : N ≅ N') :
    (Invertible.tensorProductIso O hO (Iso.refl M) b).hom = M ◁ b.hom :=
  (bridge_tensorIso O hO (Iso.refl M) b).trans (MonoidalCategory.id_tensorHom M b.hom)

/-- `bridge_tensorIso` with the second factor an identity: a right whiskering. -/
theorem bridge_tensorIso_right
    {M M' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (a : M ≅ M')
    (N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductIso O hO a (Iso.refl N)).hom = a.hom ▷ N :=
  (bridge_tensorIso O hO a (Iso.refl N)).trans (MonoidalCategory.tensorHom_id a.hom N)

/-- Tensoring on the right by `X`, the functor the integral tensor powers of Tag 01CU are
iterates of, acts on morphisms as right whiskering by `X`. -/
theorem bridge_tensorRight
    {M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : M ⟶ N)
    (X : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).flip.obj
          (X))).map g = g ▷ X :=
  sheafifyWhiskerRight_eq_comparison O hO g X

end Bridge

/-! ### A step of pure monoidal algebra -/

section MonoidalStep

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The monoidal algebra behind the inductive step of the multiplicativity square.** Given the
associativity law in the target, a degreewise family compatible with the multiplication in
bidegrees `(n, m)` and `(m, 1)` is compatible in bidegree `(n, m + 1)`. Stated in a bare
monoidal category, where the two factorizations of a tensor product of morphisms into
whiskerings, the exchange law and the naturality of the associator are the only inputs. -/
theorem monoidalStep {A B D A' B' D' M N R S : C}
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D')
    (p : B' ⊗ D' ⟶ M) (q : A' ⊗ B' ⟶ N) (s : A' ⊗ M ⟶ R) (t : N ⊗ D' ⟶ S) (u : S ⟶ R)
    (h : ((α_ A' B' D').hom ≫ (A' ◁ p)) ≫ s = ((q ▷ D') ≫ t) ≫ u) :
    (α_ A B D).hom ≫ (A ◁ ((b ⊗ₘ d) ≫ p)) ≫ (a ▷ M) ≫ s =
      ((a ⊗ₘ b) ▷ D) ≫ (q ▷ D) ≫ (N ◁ d) ≫ t ≫ u := by
  have h' : (q ▷ D') ≫ t ≫ u = (α_ A' B' D').hom ≫ (A' ◁ p) ≫ s := by
    simp only [← Category.assoc]
    exact h.symm
  have hL : (α_ A B D).hom ≫ (A ◁ ((b ⊗ₘ d) ≫ p)) ≫ (a ▷ M) ≫ s =
      (α_ A B D).hom ≫ (a ⊗ₘ (b ⊗ₘ d)) ≫ (A' ◁ p) ≫ s := by
    rw [MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc a p, ← reassoc_of% (tensorHom_def' a (b ⊗ₘ d))]
  have hR : ((a ⊗ₘ b) ▷ D) ≫ (q ▷ D) ≫ (N ◁ d) ≫ t ≫ u =
      ((a ⊗ₘ b) ⊗ₘ d) ≫ (q ▷ D') ≫ t ≫ u := by
    rw [← whisker_exchange_assoc q d, ← reassoc_of% (tensorHom_def (a ⊗ₘ b) d)]
  rw [hL, hR, h', reassoc_of% (MonoidalCategory.associator_naturality a b d)]

end MonoidalStep

/-! ### The right-tensor functor at the spelling of a scheme -/

section SchemeBridge

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X : Scheme.{u}}

/-- `bridge_tensorRight`, ascribed at the spelling of a scheme. -/
theorem tensorRight_map {M N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)}
    (g : M ⟶ N) (Z : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj Z).map g = g ▷ Z :=
  bridge_tensorRight _ _ g Z

/-- `bridge_tensorRight` for an isomorphism, ascribed at the spelling of a scheme. -/
theorem tensorRight_mapIso {M N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)}
    (e : M ≅ N) (Z : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj Z).mapIso e).hom =
      e.hom ▷ Z :=
  bridge_tensorRight _ _ e.hom Z

end SchemeBridge

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

variable {T' T : Scheme.{u}} (k : T' ⟶ T)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- Tensoring on the right by an invertible module is an equivalence, at the spelling the
integral tensor powers of Tag 01CU are indexed by. This is
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor`, restated so that instance
search reaches it from the invertibility hypothesis carried by the variables above. -/
instance isEquivalenceTensorRight :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).IsEquivalence :=
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _

/-- **The pullback `k^*L` of an invertible `𝒪_T`-module**, which is again invertible by Tag
0B8L (`Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj`). -/
abbrev pullbackModule : SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace) :=
  (pullbackFunctor (ringedSpaceHom k)).obj L

/-- **A comparison in a single degree**: an isomorphism `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` between
the degree-`n` pieces of the pullback of the Laurent algebra of `L` and of the Laurent algebra
of `k^*L`. -/
abbrev PieceCmp (n : ℤ) : Type u :=
  (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece n) ≅
    (laurent (pullbackModule k L)).piece n

/-- The pullback distributes over the extra tensor factor: `k^*(L^{⊗ n} ⊗ L) ≅ k^*(L^{⊗ n}) ⊗
k^*L`. This is the comparison of Tag 01CD, which is an isomorphism. -/
abbrev splitIso (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece n ⊗ L) ≅
      (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece n) ⊗ pullbackModule k L :=
  asIso (pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L)

/-- **Splitting off the top factor upstairs**: `k^*(L^{⊗ (n+1)}) ≅ k^*(L^{⊗ n}) ⊗ k^*L`, the
successor comparison of Tag 01CU followed by the comparison of Tag 01CD. The target is written
as the image of `k^*(L^{⊗ n})` under right tensoring by `k^*L`, which is the shape the
cancellation of `predStep` consumes. -/
def climbIso (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece (n + 1)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
        (pullbackModule k L)).obj
          ((pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece n)) :=
  (pullbackFunctor (ringedSpaceHom k)).mapIso
      (tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n).symm ≪≫
    splitIso k L n

/-- **Raising the degree by one.** Split the extra factor off by `climbIso`, apply the
comparison at `n` in the first factor, and reassemble by the successor comparison downstairs.
Nothing here uses the sign of `n`. -/
def succStep (n : ℤ) (φ : PieceCmp k L n) : PieceCmp k L (n + 1) :=
  climbIso k L n ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
      (pullbackModule k L)).mapIso φ ≪≫
    tensorPowerSuccIso T'.toRingedSpace.presheaf (isSheafStruct T') (pullbackModule k L) n

/-- **Lowering the degree by one.** There is no recursion available: the negative tensor powers
of Tag 01CU are iterates of a chosen quasi-inverse of right tensoring by `L`, and the pullback
has no reason to commute with that choice. The step is taken by cancellation instead. Tensoring
on the right by `k^*L` is an equivalence, hence fully faithful, and the two sides of the
comparison at `n` tensored by `k^*L` are, by Tags 01CD and 01CU, the two sides of the comparison
at `n + 1`; so the comparison at `n` is the unique preimage. -/
def predStep (n : ℤ) (ψ : PieceCmp k L (n + 1)) : PieceCmp k L n :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
      (pullbackModule k L)).preimageIso
    ((climbIso k L n).symm ≪≫ ψ ≪≫
      (tensorPowerSuccIso T'.toRingedSpace.presheaf (isSheafStruct T')
        (pullbackModule k L) n).symm)

/-- Tensoring the lowering step by `k^*L` undoes the cancellation it was defined by: this is
`CategoryTheory.Functor.map_preimage` for the fully faithful functor `- ⊗ k^*L`. -/
theorem mapIso_predStep (n : ℤ) (ψ : PieceCmp k L (n + 1)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
        (pullbackModule k L)).mapIso (predStep k L n ψ) =
      (climbIso k L n).symm ≪≫ ψ ≪≫
        (tensorPowerSuccIso T'.toRingedSpace.presheaf (isSheafStruct T')
          (pullbackModule k L) n).symm :=
  Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
    (pullbackModule k L)).map_preimage _)

/-- Conjugating by two isomorphisms and undoing the conjugation. Stated in a bare category, so
that the proof never has to look at the two interchangeable spellings of the category of sheaves
of modules. -/
theorem iso_conj_left {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (b : E ≅ D) (g : A ≅ D) : a ≪≫ (a.symm ≪≫ g ≪≫ b.symm) ≪≫ b = g := by
  ext; simp

/-- Undoing a conjugation by two isomorphisms, in the other order. -/
theorem iso_conj_right {C : Type*} [Category C] {A B E D : C}
    (a : A ≅ B) (b : E ≅ D) (g : B ≅ E) : a.symm ≪≫ (a ≪≫ g ≪≫ b) ≪≫ b.symm = g := by
  ext; simp

/-- Lowering and then raising the degree is the identity. -/
@[simp] theorem succStep_predStep (n : ℤ) (ψ : PieceCmp k L (n + 1)) :
    succStep k L n (predStep k L n ψ) = ψ := by
  simp only [succStep, mapIso_predStep]
  exact iso_conj_left _ _ _

/-- Raising and then lowering the degree is the identity. -/
@[simp] theorem predStep_succStep (n : ℤ) (φ : PieceCmp k L n) :
    predStep k L n (succStep k L n φ) = φ := by
  refine Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
    (pullbackModule k L)).map_injective ?_)
  have h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
        (pullbackModule k L)).mapIso (predStep k L n (succStep k L n φ)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
        (pullbackModule k L)).mapIso φ := by
    rw [mapIso_predStep]
    simp only [succStep]
    exact iso_conj_right _ _ _
  exact congrArg Iso.hom h

/-- **The comparison in degree `0`**: both sides are the structure sheaf, and the comparison is
the unit comparison `k^*𝒪_T ≅ 𝒪_{T'}` of Tag 01CD. -/
def zeroCmp : PieceCmp k L 0 :=
  letI e : (pullbackFunctor (ringedSpaceHom k)).obj
        (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))) ≅
      𝟙_ (SheafOfModules.{u} (structureRingSheaf T'.toRingedSpace)) :=
    asIso (pullbackUnitComparison (ringedSpaceHom k))
  e

/-- The comparison in the nonnegative degrees, by recursion. -/
def pieceIsoNat : (j : ℕ) → PieceCmp k L (j : ℤ)
  | 0 => zeroCmp k L
  | j + 1 => succStep k L (j : ℤ) (pieceIsoNat j)

/-- The comparison in the negative degrees, by recursion downwards from degree `0`. -/
def pieceIsoNeg : (j : ℕ) → PieceCmp k L (Int.negSucc j)
  | 0 => predStep k L (Int.negSucc 0) (zeroCmp k L)
  | j + 1 => predStep k L (Int.negSucc (j + 1)) (pieceIsoNeg j)

/-- **The comparison `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` of the integral tensor powers of Tag 01CU**,
for every integer `n`, in the spelling the Laurent algebra of Section 01NS is graded by.

This is the input the pullback of a quadruple along a morphism `T' ⟶ T` of test schemes needs.
It is **not** enough on its own: the pullback of a quadruple also needs the comparison to be
compatible with the multiplication of the Laurent algebra, which is `pieceIso_mul` below, in
every integral bidegree. See the module docstring. -/
def pieceIso : (n : ℤ) → PieceCmp k L n
  | Int.ofNat j => pieceIsoNat k L j
  | Int.negSucc j => pieceIsoNeg k L j

/-- In a nonnegative degree `j`, `pieceIso` is `pieceIsoNat`. -/
@[simp] theorem pieceIso_ofNat (j : ℕ) : pieceIso k L (j : ℤ) = pieceIsoNat k L j := rfl

/-- In a negative degree `-(j + 1)`, `pieceIso` is `pieceIsoNeg`. -/
@[simp] theorem pieceIso_negSucc (j : ℕ) :
    pieceIso k L (Int.negSucc j) = pieceIsoNeg k L j := rfl

/-- **In degree `0` the comparison is the unit comparison of Tag 01CD.** -/
theorem pieceIso_zero : pieceIso k L 0 = zeroCmp k L := rfl

/-- **The successor law, in every integral degree.** The comparison at `n + 1` is the comparison
at `n` pushed up by `succStep`. Together with `pieceIso_zero` this determines the whole family,
because `succStep` is invertible (`succStep_predStep`, `predStep_succStep`); it is the equation
that a comparison chosen from an existence statement cannot have. -/
theorem pieceIso_succ (n : ℤ) : pieceIso k L (n + 1) = succStep k L n (pieceIso k L n) := by
  match n with
  | Int.ofNat j => rfl
  | Int.negSucc 0 => exact (succStep_predStep k L (Int.negSucc 0) (zeroCmp k L)).symm
  | Int.negSucc (j + 1) =>
      exact (succStep_predStep k L (Int.negSucc (j + 1)) (pieceIsoNeg k L j)).symm

/-- **The predecessor law**: the successor law read downwards. -/
theorem pieceIso_pred (n : ℤ) : pieceIso k L n = predStep k L n (pieceIso k L (n + 1)) := by
  rw [pieceIso_succ, predStep_succStep]

/-! ### The coherence laws of the Laurent multiplication, ascribed -/

section Ascribed

/-- **The coherent multiplication `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU**, with its
type ascribed at the spelling of a scheme and with the tensor product spelled by the monoidal
product of Tag 01CA. -/
abbrev mulIso (n m : ℤ) :
    (laurent L).piece n ⊗ (laurent L).piece m ≅ (laurent L).piece (n + m) :=
  coherentMulIso T.toRingedSpace.presheaf (isSheafStruct T) L n m

/-- Reindexing a tensor power along an equality of exponents, ascribed. -/
abbrev reindexIso {n m : ℤ} (h : n = m) : (laurent L).piece n ≅ (laurent L).piece m :=
  tensorPowerReindex T.toRingedSpace.presheaf (isSheafStruct T) L h

/-- The successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` of Tag 01CU, ascribed. -/
abbrev succIso (n : ℤ) : (laurent L).piece n ⊗ L ≅ (laurent L).piece (n + 1) :=
  tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n

/-- The identification `L^{⊗ 1} = L` of Tag 01CU, ascribed. -/
abbrev oneIsoL : (laurent L).piece 1 ≅ L :=
  tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) L

/-- The degree-zero piece of the Laurent algebra is the unit object of Tag 01CA. -/
theorem piece_zero : (laurent L).piece 0 =
    𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) := rfl

/-- The successor comparison in degree zero is the identity: the zeroth power is the unit and
the first power is the unit tensored by `L`, on the nose. -/
theorem succIso_zero : succIso L 0 = Iso.refl _ := rfl

/-- The identification `L^{⊗ 1} = L` is the left unitor of Tag 01CA. -/
theorem oneIsoL_eq_leftUnitor : (oneIsoL L).hom = (λ_ L).hom :=
  bridge_leftUnitor _ _ L

/-- The right unitor of Tag 01CA, with its unit factor ascribed as the degree-zero piece of the
Laurent algebra, which is the shape the unit law of Tag 01CU is stated at. -/
abbrev rightUnitorZero (A : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    A ⊗ (laurent L).piece 0 ≅ A :=
  ρ_ A

/-- Naturality of the right unitor, ascribed. -/
theorem rightUnitorZero_naturality
    {A B : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (f : A ⟶ B) :
    (f ▷ (laurent L).piece 0) ≫ (rightUnitorZero L B).hom =
      (rightUnitorZero L A).hom ≫ f :=
  MonoidalCategory.rightUnitor_naturality f

/-- Naturality of the right unitor, ascribed, in the form a right-associated composite
consumes. -/
theorem rightUnitorZero_naturality_assoc
    {A B D : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (f : A ⟶ B) (g : B ⟶ D) :
    (f ▷ (laurent L).piece 0) ≫ (rightUnitorZero L B).hom ≫ g =
      (rightUnitorZero L A).hom ≫ f ≫ g :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ g) (rightUnitorZero_naturality L f)).trans (Category.assoc _ _ _))

/-- **The unit law of Tag 01CU on the right**, ascribed: multiplying by the zeroth power is the
right unitor. -/
theorem mulIso_zero_right (n : ℤ) :
    (mulIso L n 0).hom ≫ (reindexIso L (Int.add_zero n)).hom =
      (rightUnitorZero L ((laurent L).piece n)).hom :=
  (congrArg Iso.hom (coherentMulIso_zero_right T.toRingedSpace.presheaf (isSheafStruct T) L
    n)).trans (bridge_rightUnitor _ _ _)

/-- **The unit law of Tag 01CU on the right**, solved for the multiplication. -/
private theorem mulIso_zero_right_eq (n : ℤ) :
    (mulIso L n 0).hom =
      (rightUnitorZero L ((laurent L).piece n)).hom ≫ (reindexIso L (Int.add_zero n)).inv :=
  (Iso.eq_comp_inv _).mpr (mulIso_zero_right L n)

/-- **Multiplying by the first power is the successor comparison**, ascribed. -/
theorem mulIso_one_right (n : ℤ) :
    (mulIso L n 1).hom = ((laurent L).piece n ◁ (oneIsoL L).hom) ≫ (succIso L n).hom := by
  refine (congrArg Iso.hom (coherentMulIso_one_right T.toRingedSpace.presheaf
    (isSheafStruct T) L n)).trans ?_
  exact congrArg (fun z => z ≫ (succIso L n).hom)
    (bridge_tensorIso_left T.toRingedSpace.presheaf (isSheafStruct T) ((laurent L).piece n)
      (oneIsoL L))

/-- **The associativity law of Tag 01CU**, ascribed. -/
theorem mulIso_assoc (n m j : ℤ) :
    ((mulIso L n m).hom ▷ (laurent L).piece j) ≫ (mulIso L (n + m) j).hom =
      (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece j)).hom ≫
        ((laurent L).piece n ◁ (mulIso L m j).hom) ≫ (mulIso L n (m + j)).hom ≫
          (reindexIso L (Int.add_assoc n m j).symm).hom := by
  have h := congrArg Iso.hom (coherentMulIso_assoc T.toRingedSpace.presheaf (isSheafStruct T) L
    n m j)
  refine (congrArg (fun morphism => morphism ≫ (mulIso L (n + m) j).hom)
    (bridge_tensorIso_right T.toRingedSpace.presheaf (isSheafStruct T)
      (mulIso L n m) ((laurent L).piece j)).symm).trans (h.trans ?_)
  refine (congrArg (fun morphism => morphism ≫ _ ≫ _ ≫ _)
    (bridge_associator T.toRingedSpace.presheaf (isSheafStruct T)
      ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece j))).trans ?_
  exact congrArg (fun morphism => _ ≫ morphism ≫ _ ≫ _)
    (bridge_tensorIso_left T.toRingedSpace.presheaf (isSheafStruct T)
      ((laurent L).piece n) (mulIso L m j))

/-- The associativity law at `j = 1`, solved for the bidegree-`(n, m + 1)` multiplication. -/
theorem mulIso_assoc_one (n m : ℤ) :
    ((α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
          ((laurent L).piece n ◁ (mulIso L m 1).hom)) ≫ (mulIso L n (m + 1)).hom =
      (((mulIso L n m).hom ▷ (laurent L).piece 1) ≫ (mulIso L (n + m) 1).hom) ≫
        (reindexIso L (Int.add_assoc n m 1).symm).inv := by
  refine (Iso.eq_comp_inv _).mpr ?_
  have h := mulIso_assoc L n m 1
  simp only [Category.assoc] at h ⊢
  exact h.symm

/-- **The multiplication of the Laurent algebra as a morphism out of the tensor product sheaf is
the coherent multiplication of Tag 01CU.** `SheafOfModules.GradedAlgebra.mulSheaf` descends the
bilinear multiplication of a sheaf of graded algebras to a morphism out of the tensor product
sheaf, and the multiplication of the Laurent algebra is read off from `coherentMulIso` in the
first place; so the two are the same morphism, and this records it. It is the identification the
multiplicativity of a `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting` is stated
against, `Twisting.app_mul` being phrased with `mulSheaf` and `pieceIso_mul` with
`coherentMulIso`. -/
theorem mulHom_laurent (n m : ℤ) : mulHom (laurent L) n m = (mulIso L n m).hom := by
  refine tensor_hom_ext (fun U x y => ?_)
  rw [mulHom_tmul]
  exact mulBilinear_app T.toRingedSpace.presheaf (isSheafStruct T) L n m U x y

/-- `mulHom_laurent`, stated for `SheafOfModules.GradedAlgebra.mulSheaf` itself, which is the
spelling `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.app_mul` uses. -/
theorem mulSheaf_laurent (n m : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (laurent L) n m = (mulIso L n m).hom :=
  mulHom_laurent L n m

end Ascribed

/-! ### Multiplicativity of the comparison -/

section Multiplicativity

/-- The comparison is compatible with reindexing. -/
theorem pieceIso_reindex {n m : ℤ} (h : n = m) :
    (pullbackFunctor (ringedSpaceHom k)).map (reindexIso L h).hom ≫ (pieceIso k L m).hom =
      (pieceIso k L n).hom ≫ (reindexIso (pullbackModule k L) h).hom := by
  subst h
  change (pullbackFunctor (ringedSpaceHom k)).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The comparison is compatible with reindexing, read backwards. -/
theorem pieceIso_reindex_inv {n m : ℤ} (h : n = m) :
    (pullbackFunctor (ringedSpaceHom k)).map (reindexIso L h).inv ≫ (pieceIso k L n).hom =
      (pieceIso k L m).hom ≫ (reindexIso (pullbackModule k L) h).inv := by
  subst h
  exact pieceIso_reindex k L rfl

/-- **The comparison is compatible with the successor comparison of Tag 01CU**: this is the
successor law `pieceIso_succ` read as a commuting square, with the comparison of Tag 01CD
cancelled out. -/
theorem pieceIso_succIso (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ (pieceIso k L (n + 1)).hom =
      pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L ≫
        ((pieceIso k L n).hom ▷ pullbackModule k L) ≫
          (succIso (pullbackModule k L) n).hom := by
  rw [pieceIso_succ]
  change (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
      (((pullbackFunctor (ringedSpaceHom k)).map (succIso L n).inv ≫
            pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L) ≫
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
                (pullbackModule k L)).mapIso (pieceIso k L n)).hom ≫
            (succIso (pullbackModule k L) n).hom)) = _
  rw [tensorRight_mapIso]
  refine Eq.trans (congrArg
    (fun z => (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ z)
    (Category.assoc _ _ _)) ?_
  exact Iso.hom_inv_id_assoc
    ((pullbackFunctor (ringedSpaceHom k)).mapIso (succIso L n)) _

/-- **The comparison in degree one, computed**: the successor comparison is the identity in
degree zero, so the comparison in degree one is the comparison of Tag 01CD followed by the
structure-sheaf comparison whiskered by `k^*L`. -/
theorem pieceIso_one :
    (pieceIso k L 1).hom =
      pullbackTensorComparison (ringedSpaceHom k)
          (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))) L ≫
        (pullbackUnitComparison (ringedSpaceHom k) ▷ pullbackModule k L) := by
  change ((pullbackFunctor (ringedSpaceHom k)).map (𝟙 ((laurent L).piece 0 ⊗ L)) ≫
        pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece 0) L) ≫
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
            (pullbackModule k L)).mapIso (zeroCmp k L)).hom ≫
        𝟙 ((laurent (pullbackModule k L)).piece 1)) = _
  rw [tensorRight_mapIso, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg
    (fun z => pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece 0) L ≫ z)
    (Category.comp_id ((zeroCmp k L).hom ▷ pullbackModule k L))

/-- **The comparison is compatible with the identification `L^{⊗ 1} = L`**, which by
`oneIsoL_eq_leftUnitor` is the left unitor of Tag 01CA; so this is the left-unit coherence of
Tag 01CD. -/
theorem pieceIso_oneIso :
    (pullbackFunctor (ringedSpaceHom k)).map (oneIsoL L).hom =
      (pieceIso k L 1).hom ≫ (oneIsoL (pullbackModule k L)).hom := by
  rw [pieceIso_one, oneIsoL_eq_leftUnitor, oneIsoL_eq_leftUnitor]
  exact (pullbackTensorComparison_leftUnitor (ringedSpaceHom k) L).trans
    (Category.assoc _ _ _).symm

/-- **The multiplicativity square of the comparison in bidegree `(n, m)`**: pulling back the
coherent multiplication of Tag 01CU on the Laurent algebra of `L` and then comparing in degree
`n + m` agrees with splitting the pullback by Tag 01CD, comparing in degrees `n` and `m`, and
multiplying in the Laurent algebra of `k^*L`. -/
abbrev MulCompat (n m : ℤ) : Prop :=
  (pullbackFunctor (ringedSpaceHom k)).map (mulIso L n m).hom ≫ (pieceIso k L (n + m)).hom =
    pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) ((laurent L).piece m) ≫
      ((pieceIso k L n).hom ⊗ₘ (pieceIso k L m).hom) ≫
        (mulIso (pullbackModule k L) n m).hom

/-- **Multiplicativity in bidegree `(n, 1)`, for every integer `n`.** Multiplication by the
first power is the successor comparison, and the comparison is compatible with that
(`pieceIso_succIso`) and with the identification `L^{⊗ 1} = L` (`pieceIso_oneIso`). -/
theorem mulCompat_one (n : ℤ) : MulCompat k L n 1 := by
  change (pullbackFunctor (ringedSpaceHom k)).map (mulIso L n 1).hom ≫ _ = _
  rw [mulIso_one_right, mulIso_one_right, CategoryTheory.Functor.map_comp, Category.assoc,
    pieceIso_succIso, ← Category.assoc, pullbackTensorComparison_naturality_right,
    Category.assoc, pieceIso_oneIso]
  simp only [tensorHom_def', Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rw [whisker_exchange_assoc (pieceIso k L n).hom (oneIsoL (pullbackModule k L)).hom]

/-- Tag 01CD against the right unitor, with the unit factor ascribed as the degree-zero piece of
the Laurent algebra. -/
theorem pullbackRightUnitorZero
    (A : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    (pullbackFunctor (ringedSpaceHom k)).map (rightUnitorZero L A).hom =
      pullbackTensorComparison (ringedSpaceHom k) A ((laurent L).piece 0) ≫
        ((pullbackFunctor (ringedSpaceHom k)).obj A ◁ (pieceIso k L 0).hom) ≫
          (rightUnitorZero (pullbackModule k L)
            ((pullbackFunctor (ringedSpaceHom k)).obj A)).hom :=
  pullbackTensorComparison_rightUnitor (ringedSpaceHom k) A

/-- **Multiplicativity in bidegree `(n, 0)`, for every integer `n`** — the base case of the
induction. Multiplication by the zeroth power is the right unitor, and the comparison of Tag
01CD is compatible with the right unitor. -/
theorem mulCompat_zero (n : ℤ) : MulCompat k L n 0 := by
  change (pullbackFunctor (ringedSpaceHom k)).map (mulIso L n 0).hom ≫ _ = _
  rw [mulIso_zero_right_eq, mulIso_zero_right_eq, CategoryTheory.Functor.map_comp, Category.assoc,
    pieceIso_reindex_inv, pullbackRightUnitorZero]
  simp only [tensorHom_def', Category.assoc, rightUnitorZero_naturality_assoc]

/-- The isomorphism against which the multiplicativity square in bidegree `(n, m + 1)` is
cancelled on the right: multiply by the first power downstairs, and reindex. -/
def mulTail (n m : ℤ) :
    (laurent (pullbackModule k L)).piece (n + m) ⊗
        (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1) ≅
      (laurent (pullbackModule k L)).piece (n + (m + 1)) :=
  MonoidalCategory.whiskerLeftIso _ (pieceIso k L 1) ≪≫
    (mulIso (pullbackModule k L) (n + m) 1 ≪≫
      (reindexIso (pullbackModule k L) (Int.add_assoc n m 1).symm).symm)

/-- The isomorphism against which the multiplicativity square in bidegree `(n, m + 1)` is
cancelled on the left: the pullback of the associator followed by the pullback of multiplication
in bidegree `(m, 1)`. -/
def mulHead (n m : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).obj
        (((laurent L).piece n ⊗ (laurent L).piece m) ⊗ (laurent L).piece 1) ≅
      (pullbackFunctor (ringedSpaceHom k)).obj
        ((laurent L).piece n ⊗ (laurent L).piece (m + 1)) :=
  (pullbackFunctor (ringedSpaceHom k)).mapIso
      (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)) ≪≫
    (pullbackFunctor (ringedSpaceHom k)).mapIso
      (MonoidalCategory.whiskerLeftIso ((laurent L).piece n) (mulIso L m 1))

/-- The forward map of `mulHead` is the pullback of the associator followed by the pullback of
the whiskered multiplication in bidegree `(m, 1)`. -/
theorem mulHead_hom (n m : ℤ) :
    (mulHead k L n m).hom =
      (pullbackFunctor (ringedSpaceHom k)).map
          (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
        (pullbackFunctor (ringedSpaceHom k)).map
          ((laurent L).piece n ◁ (mulIso L m 1).hom) :=
  rfl

/-- **The left-hand side of the bidegree-`(n, m + 1)` square**, cut down by `mulHead` and
`mulTail` to the left-hand side of the bidegree-`(n, m)` square whiskered by `k^*(L^{⊗ 1})`.
The inputs are the associativity law of Tag 01CU, the bidegree-`(n, 1)` case and naturality of
the comparison of Tag 01CD in the first variable. -/
theorem mulCompat_lhs (n m : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).map
          (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
        (pullbackFunctor (ringedSpaceHom k)).map
            ((laurent L).piece n ◁ (mulIso L m 1).hom) ≫
          ((pullbackFunctor (ringedSpaceHom k)).map (mulIso L n (m + 1)).hom ≫
            (pieceIso k L (n + (m + 1))).hom) =
      pullbackTensorComparison (ringedSpaceHom k)
          ((laurent L).piece n ⊗ (laurent L).piece m) ((laurent L).piece 1) ≫
        (((pullbackFunctor (ringedSpaceHom k)).map (mulIso L n m).hom ≫
            (pieceIso k L (n + m)).hom) ▷
          (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1)) ≫
        (mulTail k L n m).hom := by
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    mulIso_assoc_one, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [pieceIso_reindex_inv]
  rw [reassoc_of% (mulCompat_one k L (n + m)),
    reassoc_of% (pullbackTensorComparison_naturality_left (ringedSpaceHom k)
      (B := (laurent L).piece 1) (mulIso L n m).hom)]
  simp only [mulTail, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.whiskerLeftIso,
    Category.assoc, tensorHom_def, MonoidalCategory.comp_whiskerRight]

/-- **The right-hand side of the bidegree-`(n, m + 1)` square**, cut down by `mulHead` and
`mulTail` to the right-hand side of the bidegree-`(n, m)` square whiskered by `k^*(L^{⊗ 1})`.
The inputs are the bidegree-`(m, 1)` case, the compatibility of the comparison of Tag 01CD with
the associator, naturality in the second variable, and `monoidalStep`. -/
theorem mulCompat_rhs (n m : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).map
          (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
        (pullbackFunctor (ringedSpaceHom k)).map
            ((laurent L).piece n ◁ (mulIso L m 1).hom) ≫
          (pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n)
              ((laurent L).piece (m + 1)) ≫
            (((pieceIso k L n).hom ⊗ₘ (pieceIso k L (m + 1)).hom) ≫
              (mulIso (pullbackModule k L) n (m + 1)).hom)) =
      pullbackTensorComparison (ringedSpaceHom k)
          ((laurent L).piece n ⊗ (laurent L).piece m) ((laurent L).piece 1) ≫
        ((pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n)
              ((laurent L).piece m) ≫
            (((pieceIso k L n).hom ⊗ₘ (pieceIso k L m).hom) ≫
              (mulIso (pullbackModule k L) n m).hom)) ▷
          (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1)) ≫
        (mulTail k L n m).hom := by
  rw [reassoc_of% (pullbackTensorComparison_naturality_right (ringedSpaceHom k)
    (A := (laurent L).piece n) (mulIso L m 1).hom)]
  rw [tensorHom_def' (pieceIso k L n).hom (pieceIso k L (m + 1)).hom]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, mulCompat_one k L m,
    MonoidalCategory.whiskerLeft_comp_assoc,
    reassoc_of% (pullbackTensorComparison_associator (ringedSpaceHom k)
      ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1))]
  simp only [mulTail, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.whiskerLeftIso,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  refine congrArg (fun z => pullbackTensorComparison (ringedSpaceHom k)
      ((laurent L).piece n ⊗ (laurent L).piece m) ((laurent L).piece 1) ≫
    (pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) ((laurent L).piece m) ▷
      (pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1)) ≫ z) ?_
  exact monoidalStep (pieceIso k L n).hom (pieceIso k L m).hom (pieceIso k L 1).hom
    (mulIso (pullbackModule k L) m 1).hom (mulIso (pullbackModule k L) n m).hom
    (mulIso (pullbackModule k L) n (m + 1)).hom (mulIso (pullbackModule k L) (n + m) 1).hom
    (reindexIso (pullbackModule k L) (Int.add_assoc n m 1).symm).inv
    (mulIso_assoc_one (pullbackModule k L) n m)

/-- **The inductive step, upwards**: multiplicativity in bidegree `(n, m)` gives it in bidegree
`(n, m + 1)`. -/
theorem mulCompat_succ {n m : ℤ} (h : MulCompat k L n m) : MulCompat k L n (m + 1) := by
  refine (Iso.cancel_iso_hom_left (mulHead k L n m) _ _).mp ?_
  rw [mulHead_hom]
  simp only [Category.assoc]
  rw [mulCompat_lhs, mulCompat_rhs, h]

/-- **The inductive step, downwards**: multiplicativity in bidegree `(n, m + 1)` gives it in
bidegree `(n, m)`. This is the direction that reaches the negative exponents, and it is where
the invertibility of the first tensor power is used: the two sides of the square in bidegree
`(n, m)` become equal after tensoring on the right by `k^*(L^{⊗ 1})`, and tensoring by an
invertible module is an equivalence, hence faithful. -/
theorem mulCompat_of_succ {n m : ℤ} (h : MulCompat k L n (m + 1)) : MulCompat k L n m := by
  have h2 := congrArg (fun z => (mulHead k L n m).hom ≫ z) h
  rw [mulHead_hom] at h2
  simp only [Category.assoc] at h2
  rw [mulCompat_lhs, mulCompat_rhs] at h2
  have h3 := (Iso.cancel_iso_hom_left (asIso (pullbackTensorComparison (ringedSpaceHom k)
    ((laurent L).piece n ⊗ (laurent L).piece m) ((laurent L).piece 1))) _ _).mp h2
  have h4 := (Iso.cancel_iso_hom_right _ _ (mulTail k L n m)).mp h3
  have : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((laurent L).piece 1) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower T.toRingedSpace.presheaf
      (isSheafStruct T) L 1
  have : Stacks.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf (isSheafStruct T')
      ((pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1)) :=
    Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj (ringedSpaceHom k)
      ((laurent L).piece 1)
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
      ((pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1))).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  refine ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T'.toRingedSpace.presheaf, T'.toRingedSpace.IsSheaf⟩).flip.obj
    ((pullbackFunctor (ringedSpaceHom k)).obj ((laurent L).piece 1))).map_injective ?_
  rw [tensorRight_map, tensorRight_map]
  exact h4

/-- **The comparison `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` of Tag 01CU is multiplicative in every
integral bidegree.** It intertwines the coherent multiplication of Tag 01CU on `L` with the one
on `k^*L`, through the comparison of Tag 01CD, for **all** integers `n` and `m` — negative ones
included.

The induction is on the second exponent, in both directions out of bidegree `(n, 0)`: upwards by
`mulCompat_succ`, downwards by `mulCompat_of_succ`. Together with `pieceIso` itself this is the
input the pullback of a quadruple of Section 01NS needs. -/
theorem pieceIso_mul (n m : ℤ) : MulCompat k L n m := by
  induction m using Int.induction_on with
  | zero => exact mulCompat_zero k L n
  | succ i ih => exact mulCompat_succ k L ih
  | pred i ih =>
      refine mulCompat_of_succ k L (n := n) (m := -(i : ℤ) - 1) ?_
      have hi : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by ring
      rw [hi]
      exact ih

end Multiplicativity

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

end
