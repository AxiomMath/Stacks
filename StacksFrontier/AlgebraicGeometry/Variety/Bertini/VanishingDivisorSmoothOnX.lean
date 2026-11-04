module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisorOpenGlue
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorSmoothThroughPoints

/-!
# The divisor of a member of the vanishing system is smooth on the whole of `X`

`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_pair`
produces, for the Bertini step of [Stacks, Tag 0FH7], a nonzero `v ∈ V_n` whose divisor is smooth
over `k` **on the open complement `X ∖ Z`** and whose germs at two closed points `x` and `x'`
avoid `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`. The source asks for more: `H_v` smooth over `k` on the whole of `X`.
The germ conditions are what buys the two missing points, and the step that spends them is the
Jacobian criterion.

That spending is possible only if the points of `Z` where no germ condition is available are
accounted for, and nothing in the statement above says there are none: it quantifies over an
arbitrary ideal sheaf `I` with `V_n` generating off `Z = |V(I)|`, so `Z` may be much larger than
`{x, x'}`. The hypothesis `Z ⊆ {x, x'}` is therefore added here, and it is consumed exactly where
one would expect — in the case division of
`AlgebraicGeometry.smooth_zeroScheme_of_smooth_comap_of_forall_notMem_maximalSqSmul`, which asks
for the germ condition at every point of `|H_v|` outside `X ∖ Z`.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.smooth_divisorOnX_of_smooth_divisor`: **the divisor on `X`
  of a member of `V_n` is smooth over `k`** when its restriction to `X ∖ Z` is and its germ at
  every point of `Z` avoids `𝔪_y²ℒ_y`.
* `Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair`: **the Bertini step
  of [Stacks, Tag 0FH7]** — for `Z ⊆ {x, x'}` there is a nonzero `v ∈ V_n` whose divisor on the
  whole of `X` is smooth over `k`, with germs at `x` and `x'` outside `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`.

## Implementation notes

`Stacks.SectionsVanishingOnSubscheme.familyDivisors` carries `V_n` on `X ∖ Z` and
`Stacks.SectionsVanishingOnSubscheme.familyDivisorsOnX` carries the same `V_n` on `X`; the divisor
of one member in the first situation is the inverse image along `(openComplement I).ι` of its
divisor in the second, which is [Stacks, Tag 0B6Y]
(`Stacks.Divisors.zeroScheme_pullback`) because the module and the section of the first situation
are the pullbacks of those of the second. That identification is what the glue lemma takes as its
equation hypothesis, and it is the whole of the passage between the two standing situations.

The regularity of the local rings of `X` is not assumed: over any field a smooth `X` has regular
local rings at all of its points
(`AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field`). The instance
`LocallyOfFiniteType (H_v ↪ X → Spec k)` is supplied by hand, as the composite of a closed
immersion with the structure morphism, as in
`Stacks.Bertini.FamilyDivisors.smooth_divisor_of_forall_notMem_maximalSqSmul`.

The reverse inclusion `{x, x'} ⊆ Z` is **not** assumed and not needed. It is what makes `x` and
`x'` lie on `H_v` — every member of `V_n` vanishes on `Z` — and so it is what the next step of
[Stacks, Tag 0FH7], the reduction of the class `[x] - [x']` to the smooth divisor, will want; it
has no part in the smoothness of `H_v`.

No `@[stacks]` attribute is attached. [Stacks, Tag 0FH7] asserts a divisibility of zero-cycle
classes after a finite separable extension; what is proved here is one step of its Bertini
reduction, and the tag's remaining steps — the geometric connectedness of `H_v`, the induction
down to a curve, the Jacobian of [Stacks, Tag 0BA0] and the étale clause of
[Stacks, Tag 03RP] — are not available.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
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

/-- **The divisor on `X` of a member of `V_n` is smooth over `k` as soon as its restriction to
`X ∖ Z` is and its germ avoids `𝔪_y²ℒ_y` at every point of `Z`.** Here `X` is smooth over a
perfect field `k`; the smoothness alone is what makes its local rings regular, and the perfection
is what the Jacobian criterion at the points of `Z` costs. `w` is any member
of the linear system `V_n` of sections of `ℒ ^⊗ n` vanishing on `Z`.

The divisor of `w` in the standing situation on `X ∖ Z` is the inverse image of its divisor in the
standing situation on `X` ([Stacks, Tag 0B6Y]), so this is
`AlgebraicGeometry.smooth_zeroScheme_of_smooth_comap_of_forall_notMem_maximalSqSmul` at the open
immersion `(openComplement I).ι`, whose range is the complement of `Z`. -/
theorem smooth_divisorOnX_of_smooth_divisor [PerfectField k] [Smooth f]
    (w : vanishingSections k f I L n)
    (hsm : Smooth (((familyDivisors k f I (L := L) n).divisor w).subschemeι ≫
      (familyDivisors k f I (L := L) n).toBase))
    (hgerm : ∀ y : X, y ∈ I.support →
      ((tensorPowModule X L n).presheaf.Γgerm y).hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) y) :
    Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) := by
  have hinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (familyDivisorsOnX k f I (L := L) n).isInvertible
  have himm : LocallyOfFiniteType
      ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι := inferInstance
  have hbase : LocallyOfFiniteType f := inferInstance
  have : LocallyOfFiniteType
      (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ himm hbase
  refine AlgebraicGeometry.smooth_zeroScheme_of_smooth_comap_of_forall_notMem_maximalSqSmul
    (tensorPowModule X L n) ((familyDivisorsOnX k f I (L := L) n).sectionOf w) f
    (openComplement I).ι
    (Stacks.Divisors.zeroScheme_pullback (openComplement I).ι (tensorPowModule X L n)
      ((familyDivisorsOnX k f I (L := L) n).sectionOf w)) hsm
    (AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field f) ?_
  intro y _ hy
  refine hgerm y ?_
  by_contra hcon
  refine hy ?_
  rw [Scheme.Opens.range_ι]
  simpa using hcon

/-- **The Bertini step of [Stacks, Tag 0FH7].** Let `X` be smooth over an algebraically closed
field `k`, let `ℒ ^⊗ n` be generated off `Z` by its sections `V_n` vanishing on `Z` with
`X ∖ Z ⟶ 𝐏(V_n)` an immersion — the two conclusions of [Stacks, Tag 0FD5] — let the whole space
`Γ(X, ℒ ^⊗ n)` generate and define an immersion, let `x` and `x'` be closed points of `X` at
which `X` has dimension `m`, with `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ m`, and let `Z ⊆ {x, x'}`. Then some
nonzero `v ∈ V_n` has

* `H_v ⊆ X` smooth over `k`, and
* germs at `x` and at `x'` outside `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`.

This is
`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_pair`,
whose smoothness conclusion is about `H_v ⊆ X ∖ Z`, promoted to a statement about `H_v ⊆ X` by
`Stacks.SectionsVanishingOnSubscheme.smooth_divisorOnX_of_smooth_divisor`. The hypothesis
`Z ⊆ {x, x'}` is what makes the two germ conditions cover every point of `Z`, and it is the one
hypothesis the preceding statement does not carry: without it `Z` may contain points at which
nothing is known. -/
theorem exists_ne_zero_smooth_divisorOnX_pair [IsAlgClosed k] [Smooth f]
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
    (hcond : Module.finrank k (subschemeSections k f I (L := L) n) ≤ m)
    (hsupport : (I.support : Set X) ⊆ {x, x'}) :
    ∃ w : vanishingSections k f I L n, w ≠ 0 ∧
      Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) ∧
      ((tensorPowModule X L n).presheaf.Γgerm x).hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x ∧
      ((tensorPowModule X L n).presheaf.Γgerm x').hom
          ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
        maximalSqSmul (tensorPowModule X L n) x' := by
  obtain ⟨w, hw0, hwsm, hwx, hwx'⟩ :=
    exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_pair k f I n hsm b hgen himm himm'
      hx hx' hdim hdim' hcond
  refine ⟨w, hw0, smooth_divisorOnX_of_smooth_divisor k f I n w hwsm ?_, hwx, hwx'⟩
  intro y hy
  rcases hsupport hy with rfl | rfl
  · exact hwx
  · exact hwx'

end Stacks.SectionsVanishingOnSubscheme

end
