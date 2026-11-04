module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmoothIrreducibleMember
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisorsOnX

/-!
# A member of the vanishing system whose divisor is smooth and in general position at two points

The Bertini step of [Stacks, Tag 0FH7] asks for a single section `v` of `ℒ ^⊗ n`, vanishing at
two chosen closed points `x` and `x'` of `X`, whose divisor `H_v` is smooth. The source splits
the requirement in two and this module joins the two halves back together:

* **away from `x` and `x'`** smoothness of `H_v` is the conclusion of [Stacks, Tag 0FD6] for the
  linear system `V_n` of sections vanishing on `Z = {x, x'}`, available through
  `Stacks.SectionsVanishingOnSubscheme.forGeneral_smooth_specializedDivisor_of_generatesOffSupport`
  from the two conclusions of [Stacks, Tag 0FD5];

* **at `x` and at `x'`** it is the general-position condition that the germ of `v` avoid
  `𝔪ₓ²ℒₓ`, available through
  `SectionsVanishingOnSubscheme.exists_nonempty_opens_notMem_maximalSqSmul_familyDivisorsOnX`.

Each half is produced as a nonempty open of the parameter space, and the two parameter spaces are
the same scheme (`Stacks.SectionsVanishingOnSubscheme.parameterBase_familyDivisorsOnX`), so the
three opens — one for smoothness, one for each point — meet in the irreducible parameter space
and a `k`-rational parameter of the intersection gives one member with all three properties.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_pair`:
  **the Bertini step of [Stacks, Tag 0FH7], as far as the available citations reach** — a nonzero
  `v ∈ V_n` whose divisor on `X ∖ Z` is smooth over `k` and whose germs at `x` and at `x'` avoid
  `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`.

## Implementation notes

The two points are taken separately rather than as one finite family, because that is how the
source uses the statement and because the only input the general-position half needs at a point
is the local dimension; the two hypotheses `hdim` and `hdim'` share the dimension `m`, which for
the geometrically irreducible `X` of [Stacks, Tag 0FH7] is no restriction.

The opens are intersected with `Stacks.Bertini.FamilyDivisors.irreducibleSpace_parameterBase` and
the two-open form of irreducibility, used twice, rather than through a finite-family lemma: the
parameter space is irreducible, so `IsPreirreducible` applied to `U ⊓ W` and `W'` is already the
statement for three opens.

The smoothness conclusion is about the divisor `H_v` as a closed subscheme of the *open
complement* `X ∖ Z`, which is where [Stacks, Tag 0FD6] puts it and where
`Stacks.SectionsVanishingOnSubscheme.familyDivisors` lives. Promoting it to a statement about
`H_v` as a closed subscheme of `X` is a separate matter and is not done here: it is exactly the
point at which the general-position conditions at `x` and `x'` are meant to be consumed, and it
needs one hypothesis the statement below does not carry — that `Z` is contained in `{x, x'}`.
Without it the ideal sheaf `I` quantified over here may cut out a `Z` with points at which no
germ condition is available, and the Jacobian criterion has nothing to say there. That promotion,
with the inclusion assumed, is
`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair`; the local criterion
it rests on is `AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField`.

## References

* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.ImmersionEvaluationSurjective

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)
  [FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L n))]
  [FiniteDimensional k (vanishingSections k f I L n)]

/-- **A nonzero member of `V_n` whose divisor is smooth away from `Z` and whose `1`-jets at two
closed points of `Z` are nonzero.** Let `X` be smooth over an algebraically closed field `k`,
let `ℒ ^⊗ n` be generated off `Z` by its sections `V_n` vanishing on `Z` with `X ∖ Z ⟶ 𝐏(V_n)` an
immersion — the two conclusions of [Stacks, Tag 0FD5] — let the whole space `Γ(X, ℒ ^⊗ n)`
generate and define an immersion, and let `x` and `x'` be closed points of `X` at which `X` has
dimension `m`, with `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ m`. Then some nonzero `v ∈ V_n` has

* `H_v ⊂ X ∖ Z` smooth over `k`, and
* germs at `x` and at `x'` outside `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`.

This is the Bertini step of [Stacks, Tag 0FH7]: there `Z` is the pair `{x, x'}`, the space of
linear conditions is two dimensional, and the hypothesis on it reads `2 ≤ m`, the dimension range
of the Bertini branch of that proof. -/
theorem exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_pair [IsAlgClosed k] [Smooth f]
    [Module.Finite k (subschemeSections k f I (L := L) n)]
    (hsm : Smooth ((openComplement I).ι ≫ f))
    {N : ℕ} (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n))
    (hgen : GeneratesOffSupport k f I L n)
    (himm : IsImmersion (toProjectiveSpaceOfVanishingSections k f b hgen))
    {p : ℕ} {b' : Module.Basis (Fin (p + 1)) k
      (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
    {hb' : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b'}
    (himm' : (ambientFamilyDivisors k f (L := L) n).IsImmersive b' hb')
    {x x' : X} (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X))
    {m : ℕ} (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hdim' : topologicalKrullDimAt X x' = (m : WithBot ℕ∞))
    (hcond : Module.finrank k (subschemeSections k f I (L := L) n) ≤ m) :
    ∃ w : vanishingSections k f I L n, w ≠ 0 ∧
      Smooth (((familyDivisors k f I (L := L) n).divisor w).subschemeι ≫
        (familyDivisors k f I (L := L) n).toBase) ∧
      ((tensorPowModule X L n).presheaf.Γgerm x).hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x ∧
      ((tensorPowModule X L n).presheaf.Γgerm x').hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x' := by
  have := (familyDivisors k f I (L := L) n).irreducibleSpace_parameterBase
  obtain ⟨U, hUne, hU⟩ :=
    forGeneral_smooth_specializedDivisor_of_generatesOffSupport k f I n hsm b hgen himm
  obtain ⟨W, hWne, hW⟩ :=
    exists_nonempty_opens_notMem_maximalSqSmul_familyDivisorsOnX k f I n himm' hx hdim hcond
  obtain ⟨W', hW'ne, hW'⟩ :=
    exists_nonempty_opens_notMem_maximalSqSmul_familyDivisorsOnX k f I n himm' hx' hdim' hcond
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : vanishingSections k f I L n,
      (familyDivisorsOnX k f I (L := L) n).evalVector x v₀ ≠ 0 := by
    by_contra! hall
    exact evalVector_ne_zero_familyDivisorsOnX k f I n himm' hx hdim hcond (LinearMap.ext hall)
  have hv₀ne : v₀ ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero _)
  have hr : 0 < Module.finrank k (vanishingSections k f I L n) :=
    Module.finrank_pos_iff.mpr ⟨⟨v₀, 0, hv₀ne⟩⟩
  have : Infinite (familyDivisors k f I (L := L) n).k := (inferInstance : Infinite k)
  have hmeet : ∀ V₁ V₂ : (familyDivisors k f I (L := L) n).parameterBase.Opens,
      (V₁ : Set (familyDivisors k f I (L := L) n).parameterBase).Nonempty →
      (V₂ : Set (familyDivisors k f I (L := L) n).parameterBase).Nonempty →
      ((V₁ ⊓ V₂ : (familyDivisors k f I (L := L) n).parameterBase.Opens) :
        Set (familyDivisors k f I (L := L) n).parameterBase).Nonempty :=
    fun V₁ V₂ h₁ h₂ => nonempty_preirreducible_inter V₁.isOpen V₂.isOpen h₁ h₂
  obtain ⟨c, hc0, hcU⟩ := (familyDivisors k f I (L := L) n).exists_parameterPoint_mem hr
    (U ⊓ W ⊓ W') (hmeet _ _ (hmeet _ _ hUne hWne) hW'ne)
  refine ⟨∑ i, c i • (familyDivisors k f I (L := L) n).basis i, fun hw => hc0 ?_,
    (familyDivisors k f I (L := L) n).smooth_divisor_of_smooth_specializedDivisor c
      (hU (familyDivisors k f I (L := L) n).k c (fun q => ((hcU q).1).1) c rfl), ?_, ?_⟩
  · exact funext (Fintype.linearIndependent_iff.mp
      (familyDivisors k f I (L := L) n).basis.linearIndependent c hw)
  all_goals erw [← (familyDivisorsOnX k f I (L := L) n).constCoeffSection_eq_sectionOf c]
  · exact hW c fun q => ((hcU q).1).2
  · exact hW' c fun q => (hcU q).2

end Stacks.SectionsVanishingOnSubscheme

end
