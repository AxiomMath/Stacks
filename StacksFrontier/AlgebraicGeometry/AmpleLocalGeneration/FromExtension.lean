module

public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.FromLocalGeneration
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineGermSpan
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.GermSpan
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Clauses (7) and (8) of Stacks Tag 01Q3, with no residual

`./Basic.lean` reduces the second half of clause (7) of [Stacks, Tag 01Q3] to one named input,
`Stacks.AmpleLocalGeneration.IsLocallyFinGenAfterSomeTwist`, and
`../AmpleEventualGeneration/FromLocalGeneration.lean` reduces the first half to the same input at
the positive tensor powers. Both files record that input as unproved, for every class of schemes.

**It is a theorem.** Its three ingredients were present and one germ computation was missing
between them; that computation is
`Stacks.SectionTensorFormula.span_germ_tensorSection_eq_top`, and a second gap — that the
module-valued form of [Stacks, Tag 01PW] returns a *different* tensor power for each section, so a
family of generators could not be assembled in one module — is closed by
`Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple`. With those,
clauses (7) and (8) hold for every quasi-compact scheme carrying an ample invertible module.

## Main results

* `Stacks.AmpleLocalGeneration.isLocallyFinGenAfterSomeTwist_of_isAmple`: **the residual is a
  theorem**, for every scheme with an ample invertible module.
* `Stacks.AmpleLocalGeneration.isFinGenAfterSomeTwist_of_isAmple` and
  `Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`: the two halves of clause (7),
  unconditionally.
* `Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple`: **clause (7) of
  [Stacks, Tag 01Q3]**, unconditionally.
* `Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`: **clause (8)**,
  unconditionally — every finite-type quasi-coherent module is a quotient of a finite direct sum
  of tensor powers `L ^⊗ (-dⱼ)` with the `dⱼ` as large as desired, with quasi-coherent kernel.

## How the three ingredients meet

Fix a quasi-coherent `F` of finite type, a degree `N ≥ 1`, a global section `s` of `L ^⊗ N` and the
affine open `V = X_s`.

1. **The local generators.** `Stacks.AffineGermSpan.exists_finite_sections_span_germ` gives
   finitely many sections `t i` of `F` over `V` whose germs span `F_x` at every `x ∈ V`. This is
   [Stacks, Tag 01PB] plus the fact that on an affine open the germs of the sections of a
   quasi-coherent module generate the stalk.
2. **The extension, with one denominator.**
   `Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple` extends the
   whole family at once: one exponent `p = N e` with `e ≥ 1`, one global section `σ` of
   `L ^⊗ p` with `X_σ = X_s`, and global sections `τ i` of `F ⊗ L ^⊗ p` with
   `τ i|_V = t i ⊗ σ|_V`. A section-by-section application of the single-section form would return
   a different `p` and a different `σ` each time, and the resulting sections would live in
   different modules.
3. **The germ computation.** `Stacks.SectionTensorFormula.span_germ_tensorSection_eq_top` says
   that the germs of the products `t i ⊗ σ|_V` span `(F ⊗ L ^⊗ p)_x` at every `x ∈ V`, because `σ`
   does not vanish there. Since the germ of `τ i` at such an `x` is the germ of `τ i|_V`, the
   global sections `τ i` witness `Stacks.AmpleLocalGeneration.IsFinGenOn (F ⊗ L ^⊗ (N e)) V`.

## Implementation notes

**The twist is `N e` on the nose, not merely a multiple of `N`.** The exponent the gluing produces
is `powDeg N' K = N' (K + 1)` for the degree-equalised `N' = N m`, so it is `N e` with
`e = m (K + 1) ≥ 1`, and the extension theorem reports it in that form. This matters because
`Stacks.AmpleLocalGeneration.IsLocallyFinGenAfterSomeTwist` asks for the twist in exactly that
shape, and no degree can be added to a twist after the fact: raising `p` to a multiple of `N`
would need a global section of `L ^⊗ (N e - p)` not vanishing on `V`, and the only sections
available are the powers of `s`, whose degrees are the multiples of `N`.

**Ampleness is used three times** and is not needed at any other point: for the finite affine
cover in one common degree that the extension theorem glues over, for the positivity of the
degrees, and — in the derivation of the first half of clause (7) — for the ampleness of the
positive tensor powers of `L` ([Stacks, Tag 01PT],
`Stacks.AmplePowers.isAmple_tensorPowModule_of_isAmple`), at which the residual is applied again.

**Quasi-separatedness is not assumed.** `../SectionExtensionNoAmple/Basic.lean` proves the same
extension statement with ampleness replaced by pointwise nonvanishing, at the cost of
`QuasiSeparatedSpace X`, and with the divisibility of the exponent recorded. That route is not
taken: the divisibility is available on the ample side too, because
`Stacks.SectionExtension.exists_common_degree_affine_cover` takes the common degree to be
`n N₀`, which it now records.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)

## The tag attribute

`@[stacks 01Q3 "clause (7)"]` and `@[stacks 01Q3 "clause (8)"]` are attached to
`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple` and
`Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple`, which state
those two clauses in the source's own wording — including the quasi-separatedness each of them
asserts, and, for clause (8), the `k` copies of a *single* `L ^⊗ (-n)` rather than summands of
varying degrees.

Tag 01Q3 asserts the equivalence of all nine of its clauses, so the label is not complete: what is
proved is the implication from clause (1), ampleness, into clauses (7) and (8). Clauses (5), (6)
and (9) are not stated anywhere, and the reverse implications are not proved here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Ample Stacks.SectionTensorFormula
open scoped Stacks.ModuleStalk Stacks.FinGenFromCover

universe u

namespace Stacks.AmpleLocalGeneration

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}}

/-- **The residual of clause (7) of [Stacks, Tag 01Q3] is a theorem.** For `L` ample, every
quasi-coherent module of finite type is, over an affine nonvanishing open `X_s` of a global
section `s` of `L ^⊗ N`, generated by finitely many global sections of `F ⊗ L ^⊗ (N e)` for some
`e ≥ 1`.

The local generators over `X_s` are
`Stacks.AffineGermSpan.exists_finite_sections_span_germ`; they are extended, all at once and over
a single denominator, by
`Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple`; and the germs of
the resulting global sections span because the denominator does not vanish on `X_s`, which is
`Stacks.SectionTensorFormula.span_germ_tensorSection_eq_top`. -/
theorem isLocallyFinGenAfterSomeTwist_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : IsLocallyFinGenAfterSomeTwist X L := by
  intro F hFqc hFft N hN s V hVset hVaff
  have := hFqc
  have := hFft
  obtain rfl : V = Stacks.AmpleTheory.powNonvanishingOpen X L N s :=
    TopologicalSpace.Opens.ext (by
      rw [hVset, Stacks.AmpleTheory.coe_powNonvanishingOpen])
  obtain ⟨I, hI, t, hspan⟩ := Stacks.AffineGermSpan.exists_finite_sections_span_germ F hVaff
  obtain ⟨p, σ, τ, ⟨e, he1, rfl⟩, hσ, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple L hL F hN s
      (κ := I) t
  refine ⟨e, he1, ⟨I, τ, hI, fun x hx => ?_⟩⟩
  have hxσ : x ∈ nonvanishingLocus (tensorPowModule X L ((N * e : ℕ) : ℤ)) σ := by
    have hx' : x ∈ (Stacks.AmpleTheory.powNonvanishingOpen X L (N * e) σ : Set X) := hσ ▸ hx
    rwa [Stacks.AmpleTheory.coe_powNonvanishingOpen] at hx'
  have hpt : ∀ i : I,
      ((F ⊗ tensorPowModule X L ((N * e : ℕ) : ℤ)).presheaf.Γgerm x).hom (τ i)
        = ((F ⊗ tensorPowModule X L ((N * e : ℕ) : ℤ)).presheaf.germ _ x hx).hom
          (tensorSection F (tensorPowModule X L ((N * e : ℕ) : ℤ)) (t i)
            (Stacks.SectionExtension.resTop _ σ)) := by
    intro i
    rw [← heq i]
    exact (TopCat.Presheaf.Γgerm_res_apply
      (F ⊗ tensorPowModule X L ((N * e : ℕ) : ℤ)).presheaf x hx (τ i)).symm
  have hmain := span_germ_tensorSection_eq_top F (tensorPowModule X L ((N * e : ℕ) : ℤ))
    (Stacks.AmpleTheory.powNonvanishingOpen X L N s) t σ hx hxσ (hspan x hx)
  simpa only [hpt] using hmain

/-- **The second half of clause (7) of [Stacks, Tag 01Q3], unconditionally**: for `L` ample, every
quasi-coherent module of finite type is generated by finitely many global sections after some
twist by `L`. -/
theorem isFinGenAfterSomeTwist_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : Stacks.AmpleEventualGeneration.IsFinGenAfterSomeTwist X L :=
  isFinGenAfterSomeTwist_of_isLocallyFinGenAfterSomeTwist X L hL
    (isLocallyFinGenAfterSomeTwist_of_isAmple L hL)

/-- **The first half of clause (7) of [Stacks, Tag 01Q3], unconditionally**: for `L` ample, the
tensor powers of `L` are generated by finitely many global sections in every sufficiently positive
degree.

The residual is applied at the positive tensor powers of `L`, which are ample by
[Stacks, Tag 01PT]. -/
@[ega "II 4.5.8" "special case"]
theorem isEventuallyFinGenPowers_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers X L :=
  Stacks.AmpleEventualGeneration.isEventuallyFinGenPowers_of_isLocallyFinGenAfterSomeTwist L hL
    fun d hd => isLocallyFinGenAfterSomeTwist_of_isAmple _
      (Stacks.AmplePowers.isAmple_tensorPowModule_of_isAmple L d hd hL)

/-- **Clause (7) of [Stacks, Tag 01Q3], unconditionally.** On a scheme carrying an ample
invertible module `L`, every finite-type quasi-coherent module becomes generated by finitely many
global sections after every sufficiently positive twist by `L`. -/
@[ega "II 4.5.5" "Implication", ega "II 4.5.8" "more general", ega "III 2.6.2.5" "partial"]
theorem isEventuallyGloballyGenerated_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : Stacks.AmpleGlobalGeneration.IsEventuallyGloballyGenerated X L :=
  Stacks.AmpleEventualGeneration.isEventuallyGloballyGenerated_of_isEventuallyFinGenPowers
    (isEventuallyFinGenPowers_of_isAmple L hL) (isFinGenAfterSomeTwist_of_isAmple L hL)

/-- **Clause (8) of [Stacks, Tag 01Q3], unconditionally.** On a scheme carrying an ample
invertible module `L`, every finite-type quasi-coherent module `F` sits in a short exact sequence
`0 → F' → ⨁_{j} L ^⊗ (-dⱼ) → F → 0` with `F'` quasi-coherent and the `dⱼ` as large as desired.

This is the shape the dévissage arguments consume. -/
theorem isQuotientOfNegativeTwists_of_isAmple (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) : Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists X L :=
  Stacks.AmpleGlobalGeneration.isQuotientOfNegativeTwists_of_isEventuallyGloballyGenerated
    (isEventuallyGloballyGenerated_of_isAmple L hL)

/-! ### The two clauses of Stacks Tag 01Q3, in the source's wording -/

/-- **Clause (7) of [Stacks, Tag 01Q3]** — the clause labelled 01QA: `X` is quasi-separated, and
for every quasi-coherent sheaf `F` of finite type on `X` there is an integer `n₀` such that
`F ⊗ L ^⊗ n` is globally generated for all `n ≥ n₀`.

Both conjuncts follow from ampleness of `L`, which is clause (1): quasi-separatedness by
[Stacks, Tag 01PV] (`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`, the affine
nonvanishing opens being a basis), and the generation by
`Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple`.

The generation is obtained in the stronger form the source does not ask for: the twist is
generated by **finitely many** global sections, not merely by all of them. -/
@[stacks 01Q3 "clause (7)",
  ega "II 4.6.8" "absolute case of (c)",
  ega "II 4.5.5" "(a) ⇒ (d)",
  ega "II 2.7.9"]
theorem quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
          ∃ σ : (F ⊗ tensorPowModule X L n).GeneratingSections, Finite σ.I :=
  ⟨Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple L hL,
    isEventuallyGloballyGenerated_of_isAmple L hL⟩

/-- **Clause (8) of [Stacks, Tag 01Q3]** — the clause labelled 01QB: `X` is quasi-separated, and
for every quasi-coherent sheaf `F` of finite type on `X` there are integers `n > 0` and `k ≥ 0`
such that `F` is a quotient of a direct sum of `k` copies of `L ^⊗ (-n)`.

The summands all carry the *same* degree `-n`, as the source's clause does; the weaker statement
with varying degrees is `Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`. The
`k` of the source is the cardinality of the index type `ι` below: a direct sum over a finite index
type is a direct sum of `Nat.card ι` copies, and the two existence statements are the same.

The proof is clause (7) at a degree `n ≥ max n₀ 1`, which makes `F ⊗ L ^⊗ n` a quotient of a
finite free module, followed by
`Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free`, which untwists: tensoring the
epimorphism `𝒪_X^{⊕ ι} ↠ F ⊗ L ^⊗ n` by `L ^⊗ (-n)` presents `F` as a quotient of
`(L ^⊗ (-n))^{⊕ ι}`. -/
@[stacks 01Q3 "clause (8)",
  ega "II 2.7.10" "exists n,k quotient",
  ega "II 4.5.5" "(a) ⇒ (d')",
  sga "6 II 2.2.3" "(iii), single L"]
theorem quasiSeparatedSpace_and_exists_epi_biproduct_of_isAmple (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) :
    QuasiSeparatedSpace X ∧ ∀ F : X.Modules, F.IsQuasicoherent →
      SheafOfModules.IsFiniteType.{u, u, u} F →
        ∃ (n : ℤ) (ι : Type u) (_ : Finite ι), 0 < n ∧
          ∃ (b : Bicone fun _ : ι => tensorPowModule X L (-n)) (_ : b.IsBilimit)
            (p : b.pt ⟶ F), Epi p := by
  refine ⟨Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple L hL, fun F hFqc hFft => ?_⟩
  obtain ⟨n₀, hgen⟩ := isEventuallyGloballyGenerated_of_isAmple L hL F hFqc hFft
  obtain ⟨σ, hfin⟩ := hgen (max n₀ 1) (le_max_left _ _)
  have : Finite σ.I := hfin
  obtain ⟨b, hb, p, hp, -⟩ := Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free L
    (max n₀ 1) F ((F ⊗ tensorPowModule X L (max n₀ 1)).freeHomEquiv.symm σ.s) σ.epi
  exact ⟨max n₀ 1, σ.I, hfin, lt_of_lt_of_le zero_lt_one (le_max_right _ _), b, hb, p, hp⟩

end Stacks.AmpleLocalGeneration

end
