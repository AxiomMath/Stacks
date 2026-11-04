module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedTildePullbackSection
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFiniteSupplement
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFinitenessSupplement

/-!
# The degreewise action of `B` on `⨁ₙ H^p(X, Fₙ)` over `f^* B̃`

Let `A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra with pieces `𝒜 n`,
`f : X ⟶ Spec A` a proper morphism and `𝓑 = f^* B̃` the graded algebra
[Stacks, Tag 0897] works over. For a graded `𝓑`-module `F`, **this file builds the action of the
*ring* `B` on `⨁_{n ≥ 0} H^p(X, Fₙ)` degreewise, the way the source defines it**: a homogeneous
element of degree `k` of `B` is a global section of `𝓑ₖ`
(`Stacks.AffineGradedAlgebra.gradedTildePullbackSection`), it multiplies `Fₙ` into `Fₙ₊ₖ`
(`SheafOfModules.GradedModule.smulSectionsHom`), and `H^p(X, −)` of that is the action on
cohomology.

This is the second half of the comparison the note on
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedCohomologySumModuleOfFiniteType` asks
for. The action that part (1) of [Stacks, Tag 0897] is proved for is *not* this one: it is the
one carried across the comparison of [Stacks, Tag 089W],
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedCohomologySumModule`. **The two are not
identified here.** What is proved is the implication: granted a `B`-linear injection of the
degreewise module into the carried one, part (1) holds for the degreewise action as well.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.gradedTildeSectionSystem`: the system of
  global homogeneous sections of `f^* B̃` indexed by the graded pieces of `B`, i.e. the
  `f^* B̃` instance of `Stacks.Cohomology.FormalFunctions.SectionSystem`.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.gradedTildeCohomologyGmodule`: **the
  degreewise graded `B`-module `⨁_{n ≥ 0} H^p(X, Fₙ)`**, as a `DirectSum.Gmodule`.
* `Stacks.AlgebraicGeometry.GradedProperCohomology.gradedTildeCohomologyModule`: the same, read
  as a `B`-module through `DirectSum.decomposeRingEquiv`.

## Main results

* `Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedTildeCohomologyModule`:
  **[Stacks, Tag 0897] part (1) for the degreewise action, granted one `B`-linear injection**
  of the degreewise module into the module part (1) is proved for. The hypothesis is the whole
  of what separates the two actions; it is data, not a `Prop`-valued stand-in, and no
  `@[stacks]` registration depends on this theorem.

## Implementation notes

The graded-module machinery is the one in
`StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite`, which is stated for
an arbitrary `Stacks.Cohomology.FormalFunctions.SectionSystem` over an arbitrary sheaf of graded
algebras; the Rees algebra `⨁ₙ ℐⁿ` of an ideal sheaf and the `f^* B̃` here are its two
instances. Only the section system is new, and its three laws are
`Stacks.AffineGradedAlgebra.eval_gradedTildePullbackSection_add`,
`eval_gradedTildePullbackSection_one` and `eval_mul_gradedTildePullbackSection`.

The machinery is phrased over a scheme *over* `Spec A`, as `X : Over (Spec A)`, because that is
how `Stacks.Cohomology.FormalFunctions.cohomologyFunctor` is phrased; the instance here is at
`Over.mk f`, whose `left` is `X` by definition. The implicit `X` of
`Stacks.Cohomology.FormalFunctions.gradedCohomologyPieceOfGrading` is not determined by
unification from the type of `F` — it occurs there only inside `X.left.ringCatSheaf` — so it is
supplied by name.

The degreewise module is indexed by `ℕ` and the module of
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedCohomologySum` by `ℤ`, the first because
the graded ring `B` is `ℕ`-graded and the second because a graded `𝓑`-module has a piece in
every integer degree. The hypothesis of the finiteness theorem therefore carries two things at
once: the compatibility of the [Stacks, Tag 089W] comparison with the degreewise action, and
the passage between all integer degrees and the nonnegative ones — which in the setting of the
source is no restriction, the graded modules there being `ℕ`-graded, but which is not proved
here either.

**Which way that passage runs is forced, and it is the reason the hypothesis is an injection.**
`B` acts degreewise by shifts `n ↦ n + k` with `k ≥ 0`, so the nonnegative-degree part is a
`B`-submodule of the whole and the inclusion `⨁_{n ≥ 0} ↪ ⨁_{n ∈ ℤ}` is `B`-linear, while the
projection the other way is not: a positive-degree scalar carries a negative degree into a
nonnegative one, so projecting and then acting differs from acting and then projecting. A
surjection `⨁_{n ∈ ℤ} ↠ ⨁_{n ≥ 0}` in its place would be a map with no reason to exist.
Finiteness travels along the injection just as well, through `Module.Finite.of_injective` over
the Noetherian `B` — `Algebra.FiniteType.isNoetherianRing` from `Algebra.FiniteType A B` and
`IsNoetherianRing A` — so nothing is lost by asking for the injection.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AffineGradedAlgebra (gradedTildeOf gradedTildePullbackSection
  eval_gradedTildePullbackSection_add eval_gradedTildePullbackSection_one
  eval_mul_gradedTildePullbackSection castHom_gradedTildePullbackSection)
open Stacks.Cohomology.FormalFunctions (SectionSystem degree_add_eq gradedCohomologyPieceOfGrading
  gradedCohomologyGmodule)
open scoped DirectSum

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

variable {X : Scheme.{u}} (A : Type u) [CommRing A] {Bg : Type u} [CommRing Bg] [Algebra A Bg]
  (𝒜 : ℕ → Submodule A Bg) [_root_.GradedAlgebra 𝒜] (f : X ⟶ Spec (CommRingCat.of A))

/-- **The system of global homogeneous sections of `𝓑 = f^* B̃` indexed by the graded pieces of
`B`.** This is the only algebra-specific input the degreewise graded module of cohomology needs,
and its three laws are the additivity, unit and multiplicativity of
`Stacks.AffineGradedAlgebra.gradedTildePullbackSection`. -/
def gradedTildeSectionSystem :
    SectionSystem (Over.mk f) (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
      (fun n => ↥(𝒜 n)) where
  sec := gradedTildePullbackSection A 𝒜 f
  eval_add b b' U := eval_gradedTildePullbackSection_add A 𝒜 f b b' U.unop
  eval_one U := eval_gradedTildePullbackSection_one A 𝒜 f U.unop
  castHom_mul b b' U := by
    obtain ⟨V⟩ := U
    rw [eval_mul_gradedTildePullbackSection A 𝒜 f b' b V]
    exact castHom_gradedTildePullbackSection A 𝒜 f (Nat.add_comm _ _) _ _ (mul_comm _ _) _ V

variable (F : _root_.SheafOfModules.GradedModule.{u, u, u}
    (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))) (p : ℕ)

/-- **The degreewise graded `B`-module `⨁_{n ≥ 0} H^p(X, Fₙ)` of [Stacks, Tag 0897].** A
homogeneous element of degree `k` of `B` acts on `H^p(X, Fₙ)` as `H^p(X, −)` of multiplication
by the corresponding global section of `𝓑ₖ = (f^* B̃)ₖ`. -/
@[instance_reducible]
def gradedTildeCohomologyGmodule :
    DirectSum.Gmodule (fun n => ↥(𝒜 n)) (gradedCohomologyPieceOfGrading (X := Over.mk f) F p) :=
  gradedCohomologyGmodule (gradedTildeSectionSystem A 𝒜 f) F p

/-- **The degreewise action read as a `B`-module structure**, through the identification
`B ≅ ⨁ₙ 𝒜 n` of `DirectSum.decomposeRingEquiv`. This is the object whose finiteness
[Stacks, Tag 0897] part (1) asserts, for the action the source defines; the action part (1) is
proved for on this branch is `gradedCohomologySumModule`, carried across the comparison of
[Stacks, Tag 089W], and the two are not identified. -/
@[instance_reducible]
def gradedTildeCohomologyModule :
    Module Bg (⨁ n, gradedCohomologyPieceOfGrading (X := Over.mk f) F p n) :=
  let := gradedTildeCohomologyGmodule A 𝒜 f F p
  Module.compHom _ (DirectSum.decomposeRingEquiv 𝒜 : Bg ≃+* ⨁ n, ↥(𝒜 n)).toRingHom

/-- **[Stacks, Tag 0897] part (1) for the degreewise action, granted one `B`-linear injection
into the action part (1) is proved for.** For `A` Noetherian, `B` a finitely generated graded
`A`-algebra, `f` proper and `F` a quasi-coherent graded `f^* B̃`-module of finite type on affine
opens: if there is an injective `B`-linear map from `⨁_{n ≥ 0} H^p(X, Fₙ)` with the degreewise
action into `⨁_{n ∈ ℤ} H^p(X, Fₙ)` with the action `gradedCohomologySumModuleOfFiniteType` —
the one carried across the comparison of [Stacks, Tag 089W] — then the degreewise graded
`B`-module is a finite `B`-module.

The hypothesis is exactly what separates the two actions, and **it is not proved here.** It
carries two things at once: the compatibility of the [Stacks, Tag 089W] comparison with the
degreewise multiplication, and the passage between all integer degrees and the nonnegative
ones. Nothing registered against a Stacks tag depends on this theorem; what it buys is that
the gap between the two actions is now a single named piece of data between two objects that
both exist, rather than a statement that cannot be written down.

**Why an injection and not a surjection.** The degreewise action shifts degrees by `k ≥ 0`, so
`⨁_{n ≥ 0} H^p(X, Fₙ)` sits inside `⨁_{n ∈ ℤ} H^p(X, Fₙ)` as a `B`-submodule, and the
inclusion is the map that exists; the projection in the opposite direction is not `B`-linear,
because a positive-degree scalar carries a negative degree into a nonnegative one.

The finiteness that is transported is
`Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedCohomologySum_gradedPullback`,
which is part (1) for the carried action and carries nothing. It travels along an injection
because `B` is Noetherian — `Algebra.FiniteType.isNoetherianRing` from `Algebra.FiniteType A B`
over the Noetherian `A` — so the finite `⨁_{n ∈ ℤ} H^p(X, Fₙ)` is a Noetherian `B`-module and
`Module.Finite.of_injective` applies. -/
theorem moduleFinite_gradedTildeCohomologyModule [IsNoetherianRing A] [Algebra.FiniteType A Bg]
    [IsProper f] (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : Stacks.Coherent.IsFiniteTypeOnAffine F) :
    letI := gradedCohomologySumModuleOfFiniteType A 𝒜 f F hqc hft p
    letI := gradedTildeCohomologyModule A 𝒜 f F p
    ∀ φ : (⨁ n, gradedCohomologyPieceOfGrading (X := Over.mk f) F p n) →ₗ[Bg]
        gradedCohomologySum F p,
      Function.Injective φ →
        Module.Finite Bg (⨁ n, gradedCohomologyPieceOfGrading (X := Over.mk f) F p n) := by
  let := gradedCohomologySumModuleOfFiniteType A 𝒜 f F hqc hft p
  let := gradedTildeCohomologyModule A 𝒜 f F p
  intro φ hφ
  have : IsNoetherianRing Bg := Algebra.FiniteType.isNoetherianRing A Bg
  have := moduleFinite_gradedCohomologySum_gradedPullback A 𝒜 f F hqc hft p
  exact Module.Finite.of_injective φ hφ

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
