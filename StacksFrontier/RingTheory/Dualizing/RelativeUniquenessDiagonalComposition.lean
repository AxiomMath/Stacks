module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.SurjectiveAnyPresentation

/-!
# The composition law for upper shriek at a retract, and [stacks 0E2D] from one isomorphism

**[stacks 0E2D] itself is proved, with nothing carried, as
`Dualizing.IsRelativeDualizingComplex.nonempty_iso` in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor`;** the reduction here is a
conditional form recorded on the way.

Let `R → A` be a flat ring map of finite presentation, `B = A ⊗[R] A`, let `p₁, p₂ : A → B` be the
two coprojections and `Δ : B → A` the multiplication map.  `Δ` is **surjective** — it is a
retraction of either coprojection — and [stacks 0BZT] for a surjective second map is
unconditional in this library
(`Dualizing.upperShriekFunctor_comp_ofSurjective`,
`Dualizing.upperShriekFunctor_comp_of_surjective`).  This file draws the consequences of that
observation for the uniqueness of relative dualizing complexes.

## Main results

* `Dualizing.nonempty_upperShriekFunctor_comp_derivedHom_iso_id` — **the composition law at a
  retract**: if `h : B → A` is surjective and `s : A → B` is a section of it, then upper shriek of
  any polynomial presentation of `s`, followed by derived Hom along `h`, is the identity functor
  of `D(A)`.  Nothing is carried and nothing is assumed: no Noetherian hypothesis, no flatness,
  no projection formula.
* `Dualizing.nonempty_iso_of_nonempty_upperShriekFunctor_section_iso` — **two sections of one
  surjection force an isomorphism**: for sections `s₁, s₂` of a surjection `h : B → A` and objects
  `K, L` of `D(A)`, a single isomorphism `s₁^!(K) ≅ s₂^!(L)` in `D(B)` already gives `K ≅ L`, with
  no hypothesis on `K` or on `L`.
* `Dualizing.nonempty_upperShriekFunctor_tensorProduct_comp_derivedHom_lmul'_iso` — upper shriek
  of `R → A ⊗[R] A` followed by `Δ^!` is upper shriek of `R → A`, as functors on all of `D(R)`.
* `Dualizing.nonempty_derivedHom_lmul'_relativeDualizingComplex_iso` —
  **`Δ^!(ω^•_{B/R}) ≅ ω^•_{A/R}`**, unconditionally.
* `Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_upperShriek_coprojection_iso` —
  **[stacks 0E2D] from the single isomorphism `p₁^!(K) ≅ p₂^!(L)`**.

## What this route is, and what it is not

`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` reduces [stacks 0E2D] to the pair of
abstract isomorphisms

`Δ^!(K₁ ⊗ᴸ_B L₂) ≅ K`  and  `Δ^!(L₂ ⊗ᴸ_B K₁) ≅ L`,

and its documentation observes that at `K = L = ω^•_{A/R}` the content of the first is the
composition law `Δ^!(ω^•_{B/R}) ≅ ω^•_{A/R}` for upper shriek along `R → B --Δ--> A`.  That
composition law is **proved here**, with nothing carried: `Δ` is surjective, so
[stacks 0BZT] applies to it as the second map of the tower, in the form for a surjective second
map, which needs no Noetherian hypothesis and holds on all of `D(R)`.  The only other input is
the independence of the presentation, [stacks 0BZJ], which is unconditional here
(`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`).

The same observation, applied to the tower `A --p--> B --Δ--> A` at a section `p` of `Δ` rather
than to `R → B --Δ--> A`, gives the composition law at a retract and with it the reduction of
[stacks 0E2D] to *one* isomorphism in `D(B)` instead of two in `D(A)`: both halves of the
uniqueness argument are `Δ^! ∘ p^! ≅ id`, read at the left coprojection on one side and at the
right one on the other, so a single identification of the two upper shrieks `p₁^!(K)` and
`p₂^!(L)` closes it.  As in
`Dualizing.nonempty_iso_of_nonempty_derivedHom_tensor_iso`, no hypothesis on `K` or `L` is used.

**This hypothesis and the pair carried in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` are independent, and the reduction
claimed here is not that one made weaker.** `p₁^!(K)` is the external product `K ⊠_R ω^•_{A/R}`
and `p₂^!(L)` is `ω^•_{A/R} ⊠_R L`, but identifying them with the tensor products that appear in
that file is exactly [stacks 0BZU] — `p^!` is `p^*(-) ⊗ᴸ_B p^!(A)`, available here as
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct` —
together with [stacks 0BZV] case (2) for `p^!(A) ≅ p₂^*(ω^•_{A/R})`, which carries
`Dualizing.PolynomialPresentation.ProjectionCompatibility`, and with a comparison between
`Dualizing.derivedTensorProductOver` and the derived tensor product of the internal-Hom model.
That last comparison is *not stated* in this library, but it is not an obstruction either: both
models are pinned at K-flat representatives — the tensor comparison of the internal-Hom model's
`DerivedHomData` on one side, and the invertibility of the left-derived comparison at a K-flat
complex together with `directTensorComparison` on the other — so it is available in principle,
and `StacksFrontier.Homology.HomComplex.Evaluation.Iterated` carries it out, privately and for a
single ring, in the case of a module placed in degree zero.  None of that is used below, and so
none of it conditions the statements here; but it is why the hypothesis below is not the one
carried there made weaker, nor conversely.

## What the remaining hypothesis is worth

Granting [stacks 0BZU] and [stacks 0BZV] — that is, granting `p₁^!(K) ≅ p₁^*K ⊗ᴸ_B p₂^*ω^•_{A/R}`
— the composition law proved here discharges **exactly one** of the two isomorphisms that file
carries, namely the one at `L = ω^•_{A/R}`, and the one it leaves is *provably equivalent to the
conclusion*: `Δ^!(p₁^*K ⊗ᴸ_B p₂^*ω^•_{A/R}) ≅ ω^•_{A/R}` and
`Δ^!(p₁^*K ⊗ᴸ_B p₂^*ω^•_{A/R}) ≅ K` hold of the same object of `D(A)`, so either one of them
together with the composition law gives `K ≅ ω^•_{A/R}`, which is the tag.  The asymmetry is
structural: a composition law of the form `Δ^! ∘ p^! ≅ id` can only ever return the factor that
is *not* the relative dualizing complex of `p`, because that factor is what `p^!` was applied to.
Reading it in the other slot is the projection formula for `Δ^!` at a tensor factor pulled back
along a section of `Δ`, which is the step
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed` identifies as the content of its
hypothesis and which is not supplied by any composition law.

The same accounting applies to the single isomorphism carried below.  It is one isomorphism rather
than two and it mentions no comparison map, no tensor product and no relative dualizing complex;
but granting [stacks 0BZU], [stacks 0BZV] and [stacks 0E2E] — so that `p₁^!(K)` is
`K ⊠_R ω^•_{A/R}`, that `p₂^!(L)` is `ω^•_{A/R} ⊠_R L`, and that `ω^•_{A/R}` is itself a relative
dualizing complex — the tag applied to the pairs `(K, ω^•_{A/R})` and `(L, ω^•_{A/R})` returns the
hypothesis, so it is not independent of the conclusion either.  What is unconditional here is the
*composition law*, and that is the part of the argument this file contributes.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

-- as in `StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal`, the import
-- closure brings further `HasDerivedCategory` instances into scope, so the standard one is given
-- priority
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

section Retract

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The composition law for upper shriek at a retract.**  Let `h : B → A` be a surjective ring
homomorphism and let `s : A → B` be a section of it.  Then upper shriek of any polynomial
presentation of `s`, followed by derived Hom along `h`, is the identity functor of `D(A)`:

`h^! ∘ s^! ≅ (h ∘ s)^! = id^! = id`.

No Noetherian or flatness hypothesis is assumed, unlike the finite-type form of [stacks 0BZT].
The proof combines [stacks 0BZT] for a *surjective* second map
(`Dualizing.PolynomialPresentation.upperShriekFunctor_comp_derivedHom`), the independence of the
presentation [stacks 0BZJ] (`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`)
to compare the induced presentation of `h ∘ s`, which has as many variables as the presentation
of `s`, with the presentation of `h ∘ s = id` by no variables, and [stacks 0C0G] for a surjection
(`Dualizing.upperShriekFunctor_ofSurjective_iso_derivedHom`) to recognise the latter as derived
Hom along the identity, which is the identity. -/
theorem nonempty_upperShriekFunctor_comp_derivedHom_iso_id
    (h : B →+* A) (hh : Function.Surjective h) {s : A →+* B}
    (hs : h.comp s = RingHom.id A) (q : PolynomialPresentation s) :
    Nonempty (q.upperShriekFunctor.{u, 0} ⋙ derivedHom.{u, 0} h ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A))) := by
  have hsurj : Function.Surjective (h.comp s) := by
    rw [hs]
    exact fun a => ⟨a, rfl⟩
  obtain ⟨eComp⟩ := q.upperShriekFunctor_comp_derivedHom.{u, 0} h hh
  obtain ⟨eVars⟩ := PolynomialPresentation.nonempty_upperShriekFunctor_iso.{u, 0} (h.comp s)
    (q.compSurjective h hh) (PolynomialPresentation.ofSurjective (h.comp s) hsurj)
  obtain ⟨eNoVars⟩ := upperShriekFunctor_ofSurjective_iso_derivedHom.{u, 0} (h.comp s) hsurj
  exact ⟨eComp ≪≫ eVars ≪≫ eNoVars ≪≫ DiagonalCondition.derivedHomIsoIdOfEq (h.comp s) hs⟩

/-- **Two sections of one surjection force an isomorphism.**  Let `h : B → A` be surjective, let
`s₁` and `s₂` be sections of `h` with polynomial presentations `q₁` and `q₂`, and let `K` and `L`
be objects of `D(A)`.  A single isomorphism `s₁^!(K) ≅ s₂^!(L)` in `D(B)` gives `K ≅ L`.

No hypothesis on `K` or on `L` is used: both sides are brought down to `D(A)` by the composition
law `Dualizing.nonempty_upperShriekFunctor_comp_derivedHom_iso_id`, which is the identity on
either side, so applying derived Hom along `h` to the given isomorphism is the whole proof.  This
is the shape in which [stacks 0E2D] is reached below, at `B = A ⊗[R] A`, `h` the multiplication
map and `s₁, s₂` the two coprojections. -/
theorem nonempty_iso_of_nonempty_upperShriekFunctor_section_iso
    (h : B →+* A) (hh : Function.Surjective h) {s₁ s₂ : A →+* B}
    (hs₁ : h.comp s₁ = RingHom.id A) (hs₂ : h.comp s₂ = RingHom.id A)
    (q₁ : PolynomialPresentation s₁) (q₂ : PolynomialPresentation s₂)
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (e : Nonempty (q₁.upperShriekFunctor.{u, 0}.obj K ≅ q₂.upperShriekFunctor.{u, 0}.obj L)) :
    Nonempty (K ≅ L) := by
  obtain ⟨e₁⟩ := nonempty_upperShriekFunctor_comp_derivedHom_iso_id h hh hs₁ q₁
  obtain ⟨e₂⟩ := nonempty_upperShriekFunctor_comp_derivedHom_iso_id h hh hs₂ q₂
  exact ⟨(e₁.app K).symm ≪≫ (derivedHom.{u, 0} h).mapIso e.some ≪≫ e₂.app L⟩

end Retract

section Diagonal

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The multiplication map `A ⊗[R] A → A` is surjective: either coprojection is a section of
it. -/
theorem surjective_lmul' :
    Function.Surjective (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom := fun a =>
  ⟨(Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) a,
    congrFun (congrArg DFunLike.coe (lmul'_comp_includeLeftRingHom R A)) a⟩

/-- The multiplication map `A ⊗[R] A → A` is a map of `R`-algebras: composing it with the
structure map of `A ⊗[R] A` returns the structure map of `A`. -/
theorem lmul'_comp_algebraMap_tensorProduct :
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.comp
      (algebraMap R (A ⊗[R] A)) = algebraMap R A := by
  ext r
  simp

/-- **Upper shriek of `R → A ⊗[R] A`, followed by `Δ^!`, is upper shriek of `R → A`.**  The
multiplication map `Δ : A ⊗[R] A → A` is surjective and `Δ ∘ (R → A ⊗[R] A) = (R → A)`, so this
is [stacks 0BZT] for a surjective second map at the tower `R → A ⊗[R] A --Δ--> A`, together with
the independence of the presentation [stacks 0BZJ] to compare the induced presentation of the
composite with the given presentation `pA`.

The isomorphism is of functors on all of `D(R)`, not only on `D⁺(R)`: the restriction in the
source comes from the flat base change comparison of [stacks 0BZM], which is used to move the
variables of the second presentation past the first derived Hom, and a surjection has none. -/
theorem nonempty_upperShriekFunctor_tensorProduct_comp_derivedHom_lmul'_iso
    (pB : PolynomialPresentation (algebraMap R (A ⊗[R] A)))
    (pA : PolynomialPresentation (algebraMap R A)) :
    Nonempty (pB.upperShriekFunctor.{u, 0} ⋙
        derivedHom.{u, 0} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom ≅
      pA.upperShriekFunctor.{u, 0}) := by
  obtain ⟨eComp⟩ := pB.upperShriekFunctor_comp_derivedHom.{u, 0}
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (surjective_lmul' R A)
  exact ⟨eComp ≪≫ (PolynomialPresentation.nonempty_upperShriekFunctor_iso.{u, 0} _
    (pB.compSurjective _ (surjective_lmul' R A))
    { variableCount := pA.variableCount
      toRingHom := pA.toRingHom
      commutes := pA.commutes.trans (lmul'_comp_algebraMap_tensorProduct R A).symm
      surjective := pA.surjective }).some⟩

/-- **`Δ^!(ω^•_{B/R}) ≅ ω^•_{A/R}`**, where `B = A ⊗[R] A` and `Δ` is the multiplication map:
derived Hom along the multiplication map carries the relative dualizing complex of `R → A ⊗[R] A`
to the relative dualizing complex of `R → A`.

This is the value at the base ring of
`Dualizing.nonempty_upperShriekFunctor_tensorProduct_comp_derivedHom_lmul'_iso`, and it is
unconditional.  It is the content, at `K = L = ω^•_{A/R}`, of the hypothesis carried by
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso` of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed`; see the documentation of this module
for what identifying the two would still need and for why the composition law does not by itself
discharge that hypothesis. -/
theorem nonempty_derivedHom_lmul'_relativeDualizingComplex_iso
    (pB : PolynomialPresentation (algebraMap R (A ⊗[R] A)))
    (pA : PolynomialPresentation (algebraMap R A)) :
    Nonempty
      ((derivedHom.{u, 0} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          (pB.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        pA.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) :=
  ⟨(nonempty_upperShriekFunctor_tensorProduct_comp_derivedHom_lmul'_iso R A pB pA).some.app _⟩

/-- **[stacks 0E2D] from the single isomorphism `p₁^!(K) ≅ p₂^!(L)`.**  Let `R → A` be a flat ring
map of finite presentation, let `K` and `L` be relative dualizing complexes for it, and write
`p₁, p₂ : A → A ⊗[R] A` for the two coprojections.  If upper shriek of the left coprojection at
`K` and upper shriek of the right coprojection at `L` are isomorphic in `D(A ⊗[R] A)` — at any
polynomial presentations of the two coprojections — then `K` and `L` are isomorphic.

Both coprojections are sections of the multiplication map `Δ`, which is surjective, so
`Δ^! ∘ p₁^! ≅ id` and `Δ^! ∘ p₂^! ≅ id` by
`Dualizing.nonempty_upperShriekFunctor_comp_derivedHom_iso_id`, and the conclusion is the given
isomorphism read down in `D(A)`.  The hypotheses `hK` and `hL` are recorded rather than consumed:
`Dualizing.nonempty_iso_of_nonempty_upperShriekFunctor_section_iso` needs nothing of `K` or `L`.

The hypothesis is one isomorphism rather than the two carried by
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex_mixed_of_derivedHom_tensor_iso`, and it
names no comparison map, no tensor product and no relative dualizing complex; the two hypotheses
are nonetheless independent, and this one is not independent of the conclusion either.  See the
module documentation, which measures both. -/
theorem nonempty_iso_of_isRelativeDualizingComplex_mixed_of_upperShriek_coprojection_iso
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (q₁ : PolynomialPresentation
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A))
    (q₂ : PolynomialPresentation
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom)
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L)
    (hiso : Nonempty
      (q₁.upperShriekFunctor.{u, 0}.obj K ≅ q₂.upperShriekFunctor.{u, 0}.obj L)) :
    Nonempty (K ≅ L) := by
  have := hK
  have := hL
  exact nonempty_iso_of_nonempty_upperShriekFunctor_section_iso
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (surjective_lmul' R A)
    (lmul'_comp_includeLeftRingHom R A) (lmul'_comp_includeRight R A) q₁ q₂ hiso

end Diagonal

end

end Dualizing

end
