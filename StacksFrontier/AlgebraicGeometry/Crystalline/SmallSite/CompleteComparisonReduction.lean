module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompleteComparisonStatements
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism

/-!
# [Stacks, Tag 07MZ] reduced to the `R lim` presentation its own proof cites

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompleteComparisonStatements.lean` states the
cohomological conclusion of [Stacks, Tag 07MZ] as
`Crystalline.GlobalCrystallineSituation.SmallSite.DeRhamComparison07MZ` and proves nothing about
it.  This file measures how far that statement is from the inputs the source's own hints name: it
proves `DeRhamComparison07MZ` from one named proposition, `DerivedLimitPresentation07MZ`, and from
nothing else.

The source's hint for clause (2) is a three-step argument.  Both sides of
`RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` are `R lim` of their reductions modulo `p^e` —
the left by [Stacks, Tag 07MV], the right by the theorem on formal functions,
[Stacks, Tag 02OC] — and the two towers of reductions agree levelwise by [Stacks, Tag 07MW].  The
conclusion then follows because a derived limit is determined up to isomorphism by its tower.
That last step is the content of this file, and it is the only step here: the two `R lim`
presentations and the levelwise agreement are exactly what `DerivedLimitPresentation07MZ` asserts
and exactly what is not proved.

## The statement of [Stacks, Tag 07MZ]

> Let `p` be a prime number.  Let `(A, I, γ)` be a divided power ring with `A` a Noetherian
> `p`-adically complete ring and `p` nilpotent in `A/I`.  Set `S = Spec(A)` and `S₀ = Spec(A/I)`.
> Let `Y` be a proper smooth scheme over `S` and set `X = Y ×_S S₀`.  Let `ℱ` be a finite type
> crystal in quasi-coherent `𝒪_{X/S}`-modules.  Then
>
> 1. there exists a coherent `𝒪_Y`-module `ℱ_Y` endowed with integrable connection
>    `∇ : ℱ_Y ⟶ ℱ_Y ⊗_{𝒪_Y} Ω_{Y/S}` such that `ℱ_Y/p^eℱ_Y` is the module with connection over
>    `A/p^eA` found in Remark [Stacks, Tag 07MW], and
> 2. we have `RΓ(Cris(X/S), ℱ) = RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` in `D(A)`.
>
> Hints: the existence of `ℱ_Y` is Grothendieck's existence theorem.  The isomorphism of
> cohomologies follows as both sides are computed as `R lim` of the versions modulo `p^e` (see
> [Stacks, Tag 07MV] for the left hand side; use the theorem on formal functions,
> [Stacks, Tag 02OC], for the right hand side).  Each of the versions modulo `p^e` are isomorphic
> by [Stacks, Tag 07MW].

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `DerivedLimitPresentation07MZ` — **the three inputs the source's hint cites, as one
  proposition**: for every finite type crystal in quasi-coherent `𝒪_{X/S}`-modules there are a
  coherent `𝒪_Y`-module with integrable connection and two towers in `D(A)` such that
  `RΓ(Cris(X/S), ℱ)` is a derived limit of the first, `RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` is a derived
  limit of the second, and the two towers are pro-isomorphic.

## Main results

* `nonempty_iso_of_isDerivedLimit_plus` — two objects of `D⁺(𝒜)` that are derived limits of
  pro-isomorphic towers in `D(𝒜)` are isomorphic **in `D⁺(𝒜)`**.
* `deRhamComparison07MZ_of_derivedLimitPresentation` — **`DeRhamComparison07MZ` follows from
  `DerivedLimitPresentation07MZ`, and from nothing else.**

## What is and is not proved

**Nothing here proves [Stacks, Tag 07MZ], and no tag attribute is placed in this file.**
`DerivedLimitPresentation07MZ` is a proposition and is not discharged anywhere; it is the
hypothesis of the one reduction below.  What is proved is that it is the *only* missing input to
the already-stated `DeRhamComparison07MZ` — in particular that no further comparison between the
crystalline and de Rham sides is needed once the two towers and their levelwise agreement are
available.

What the reduction contributes mathematically is the last step of the source's hint, which is not
a formality in the derived category: a derived limit is unique only up to non-canonical
isomorphism, so the passage from "the two towers agree" to "the two limits agree" is
`Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism`, [Stacks, Tag 0H9L], and it produces
an unspecified isomorphism rather than a canonical one.  That is why both this file's conclusion
and `DeRhamComparison07MZ` are phrased with `Nonempty` of an isomorphism type: the source's `=` in
`D(A)` is an isomorphism with no claim of canonicity, and asserting a chosen isomorphism would be
asserting more than the remark does.

The derived limits are taken in the unbounded `D(A)`, not in `D⁺(A)`, because `R lim` of a tower
of bounded below objects is in general not bounded below — see the module documentation of
`StacksFrontier/Algebra/Homology/DerivedCategory/DerivedLimits.lean`.  Both sides of the comparison
are objects of `D⁺(A)`, so `nonempty_iso_of_isDerivedLimit_plus` carries the isomorphism back
across `CategoryTheory.DerivedCategory.Plus.ι`, which is fully faithful.  Stating the hypothesis
in `D⁺(A)` instead would have assumed the towers' products to exist there, which is a strictly
stronger assumption and would have made the reduction a weaker result.

The levelwise agreement is asked for as a **pro-isomorphism** of towers, `ProIso`, rather than an
isomorphism.  This is weaker than what [Stacks, Tag 07MW] supplies, so the reduction is
correspondingly stronger; an isomorphism of towers gives one by `ProIso.ofNatIso` of
`StacksFrontier/Homology/DerivedCategory/InverseSystem/ProIsomorphismInterleaving.lean`.

**The mod-`p^e` conjunct of clause (1) is still absent**, because `DeRhamComparison07MZ` is the
statement being reduced and that conjunct was already dropped from it.  The reduction therefore
measures the distance to that statement, which is strictly weaker than the remark: it does
not say *which* coherent module with connection works.  The three layers of missing vocabulary
that keep the conjunct unstatable — no bridge from a crystal to a
`AlgebraicGeometry.Scheme.Hom.ModuleConnection` on its restriction, no bridge from
`Situation07MZ` to the `p`-adic level situations of
`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelSite.lean`, and no reduction
`ℱ_Y/p^eℱ_Y` of a sheaf of `𝒪_Y`-modules at all — are named with the declarations that do exist
beside them in the "What is and is not proved" section of `CompleteComparison.lean`.  Nothing in
this file removes any of them, and `DerivedLimitPresentation07MZ` does not assert them: its towers
are existentially quantified, so it asks for the two `R lim` presentations without naming the
objects the levels are, which is why it can be written at all.

Grothendieck's existence theorem, the fourth input the hint names, is absorbed into the
existential over `Situation07MZ.CoherentModuleWithConnection` in both the hypothesis and the
conclusion; it is not separately stated here, and the type quantified over is known to be
inhabited by `Situation07MZ.structureCoherentModuleWithConnection` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/StructureSheafModuleWithConnection.lean`.

## References

* [Stacks Project, Tag 07MZ](https://stacks.math.columbia.edu/tag/07MZ)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe w w' v' u' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Derived limits and the bounded below derived category -/

section Plus

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]

/-- **Two objects of `D⁺(𝒜)` that are derived limits of pro-isomorphic towers in `D(𝒜)` are
isomorphic in `D⁺(𝒜)`.**

Derived limits of pro-isomorphic towers are non-canonically isomorphic in the ambient
pre-triangulated category by `Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism`,
[Stacks, Tag 0H9L].  That gives an isomorphism in `D(𝒜)` between the images of `X` and `Y`, and
`CategoryTheory.DerivedCategory.Plus.ι` is fully faithful, so the isomorphism descends to
`D⁺(𝒜)`.

The towers live in `D(𝒜)` rather than `D⁺(𝒜)` because a derived limit of bounded below objects
need not be bounded below; it is only the two objects being compared that are. -/
theorem nonempty_iso_of_isDerivedLimit_plus {X Y : DerivedCategory.Plus 𝒜}
    (K L : CategoryTheory.Functor ℕᵒᵖ (DerivedCategory 𝒜))
    [HasProduct fun n : ℕ => K.obj (op n)] [HasProduct fun n : ℕ => L.obj (op n)]
    (hK : Pretriangulated.IsDerivedLimit K (DerivedCategory.Plus.ι.obj X))
    (hL : Pretriangulated.IsDerivedLimit L (DerivedCategory.Plus.ι.obj Y))
    (a : InverseSequence.ProIso K L) : Nonempty (X ≅ Y) := by
  obtain ⟨f⟩ :=
    Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism K L _ _ hK hL a
  exact ⟨DerivedCategory.Plus.ι.preimageIso f⟩

end Plus

/-! ### The inputs of [Stacks, Tag 07MZ], and the reduction to them -/

section Reduction

variable (S : GlobalCrystallineSituation.{u}) (T : Situation07MZ S)
  [HasDerivedCategory.{w} (ModuleSheaf S)]
  [HasDerivedCategory.{w} T.TwistedModules]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤))]

/-- **The inputs the hint of [Stacks, Tag 07MZ] cites, as one proposition.**  For every finite
type crystal in quasi-coherent `𝒪_{X/S}`-modules `ℱ` there are a coherent `𝒪_Y`-module with
integrable connection `ℱ_Y` and two towers `K`, `L` in `D(A)` with countable products such that

* `RΓ(Cris(X/S), ℱ)` is a derived limit of `K` — the left hand side of the hint, which the source
  gets from [Stacks, Tag 07MV];
* `RΓ(Y, ℱ_Y ⊗_{𝒪_Y} Ω^•_{Y/S})` is a derived limit of `L` — the right hand side, which the
  source gets from the theorem on formal functions, [Stacks, Tag 02OC];
* `K` and `L` are pro-isomorphic — the levelwise agreement of the reductions modulo `p^e`, which
  the source gets from [Stacks, Tag 07MW].

The towers are existentially quantified rather than built, which is what makes this writable: the
objects `RΓ(Cris(X/S_e), ℱ_e)` and `RΓ(Y, ℱ_Y/p^eℱ_Y ⊗ Ω^•)` the source's levels really are have
no spelling in this library, for the reasons set out in the module documentation of
`CompleteComparison.lean`.  Nothing is lost by the quantification, because the source's argument
uses the levels only through the two limits and the comparison between them.

Pro-isomorphism, `ProIso`, is weaker than the isomorphism [Stacks, Tag 07MW] actually supplies, so
asking only for it makes the reduction below stronger.

This is a proposition, not a theorem: nothing in this file proves it, and it carries no tag
attribute. -/
def DerivedLimitPresentation07MZ : Prop :=
  ∀ F : _root_.SheafOfModules.{u} (structureSheaf S), IsFiniteTypeQuasicoherentCrystal F →
    ∃ (M : T.CoherentModuleWithConnection)
      (K L : CategoryTheory.Functor ℕᵒᵖ
        (DerivedCategory (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤))))
      (hK : HasProduct fun n : ℕ => K.obj (op n))
      (hL : HasProduct fun n : ℕ => L.obj (op n)),
      haveI := hK; haveI := hL;
      Pretriangulated.IsDerivedLimit K
          (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S F)) ∧
        Pretriangulated.IsDerivedLimit L
          (DerivedCategory.Plus.ι.obj (T.derivedBaseGlobalSections M.complex)) ∧
        Nonempty (InverseSequence.ProIso K L)

/-- **The cohomological conclusion of [Stacks, Tag 07MZ] follows from the `R lim` presentation its
hint cites, and from nothing else.**

Given, for a finite type crystal in quasi-coherent `𝒪_{X/S}`-modules, a coherent `𝒪_Y`-module
with integrable connection and two pro-isomorphic towers of which the two sides of the comparison
are derived limits, the two sides are isomorphic: this is `nonempty_iso_of_isDerivedLimit_plus`,
which is uniqueness of derived limits ([Stacks, Tag 0H9L]) together with full faithfulness of
`D⁺(A) ⟶ D(A)`.

This measures the gap between `DeRhamComparison07MZ` and the source's hint.  It is not a proof of
[Stacks, Tag 07MZ]: `DerivedLimitPresentation07MZ` is not discharged, and the statement reduced to
it is itself weaker than the remark, lacking the mod-`p^e` conjunct of clause (1).  See the module
documentation. -/
theorem deRhamComparison07MZ_of_derivedLimitPresentation
    (h : DerivedLimitPresentation07MZ S T) : DeRhamComparison07MZ S T := by
  intro F hF
  obtain ⟨M, K, L, hK, hL, hlimK, hlimL, ⟨a⟩⟩ := h F hF
  have := hK
  have := hL
  exact ⟨M, nonempty_iso_of_isDerivedLimit_plus K L hlimK hlimL a⟩

end Reduction

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
