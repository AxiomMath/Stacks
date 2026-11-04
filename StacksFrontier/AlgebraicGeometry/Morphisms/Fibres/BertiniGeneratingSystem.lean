module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniRationalPointOpen

/-!
# The generation hypothesis of the Bertini theorems

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]): a scheme `X` over a
field `k`, an invertible module `L` on it, and a finite dimensional linear system
`ψ : V → Γ(X, L)` with a chosen basis `v₁, …, v_r`. Hypothesis (2) of [Stacks, Tag 0FD6] is that
*the image of `ψ` generates `L`*, and this module states that hypothesis for a
`Stacks.Bertini.FamilyDivisors` and derives the three forms of it that the proof of the tag
consumes:

* the stalkwise generation `Stacks.ProjectiveFromSections.GeneratesStalks` of the family
  `ψ(v₁), …, ψ(v_r)`, which is the hypothesis of the morphism `φ_{L,ψ} : X → 𝐏(V)` of
  [Stacks, Tag 0FCY];
* the same for *any* basis of `V`, since the morphism to `𝐏(V)` is built from a basis indexed by
  `Fin (n + 1)` and the standing situation's own basis is indexed by `Fin (dim V)`;
* the emptiness of the common zero locus `Z = ⋂_{v ∈ V} H_v`, which is how the hypothesis enters
  the chart computations of `BertiniRationalPointOpen.lean`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.GeneratesBy` says that the sections of a family of vectors of
  the linear system generate every stalk of `L`.
* `Stacks.Bertini.FamilyDivisors.Generates` is **hypothesis (2) of [Stacks, Tag 0FD6]**: the
  image of `ψ` generates `L`. It is the case of `GeneratesBy` where the family is all of `V`, so
  it mentions no basis.
* `Stacks.Bertini.FamilyDivisors.basisSections` is the family `ψ(v₁), …, ψ(v_r)` of the chosen
  basis.

## Main results

* `Stacks.Bertini.FamilyDivisors.generatesBy_of_mem_span`: generation passes from a family to
  any family whose `k`-span contains it. Vanishing at a point is a `k`-linear condition on
  sections, so generation depends only on the subspace of `V` spanned by the family.
* `Stacks.Bertini.FamilyDivisors.generates_iff_generatesBy_of_span_eq_top` and
  `Stacks.Bertini.FamilyDivisors.generates_iff_generatesBy_basis`: hypothesis (2) is equivalent
  to generation by any spanning family, in particular by any basis. **This is what lets the
  hypothesis be stated once, basis free, and consumed at whichever basis the morphism to `𝐏(V)`
  is built from.**
* `Stacks.Bertini.FamilyDivisors.generatesBy_basis` and
  `Stacks.Bertini.FamilyDivisors.generatesStalks_basisSections`: the two forms in which the
  hypothesis is handed to [Stacks, Tag 0FCY].
* `Stacks.Bertini.FamilyDivisors.generatesBy_basis_of_generatesBy`: the hypothesis carried from
  one basis of the linear system to another, which is what a consumer transporting hypothesis (3)
  between bases needs so as not to carry a second generation hypothesis.
* `AlgebraicGeometry.notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen`: a point where a
  global section of an invertible module does not vanish is outside the support of its zero
  scheme.
* `Stacks.Bertini.FamilyDivisors.commonZeroSet_eq_empty_of_generates`: under hypothesis (2) the
  common zero locus of the linear system is empty.
* `Stacks.Bertini.FamilyDivisors.exists_rationalPointCoeff_ne_zero_of_generates` and
  `Stacks.Bertini.FamilyDivisors.nonempty_rationalPointOpen_of_generates`: hypothesis (2) makes
  the open `D(∑ᵢ cᵢxᵢ)` of a `k`-point of a trivializing chart nonempty. This is the bridge from
  the hypothesis to `BertiniRationalPointOpen.lean`, which until now took the stronger
  conclusion "the point is outside `Z`" as an input.

## Implementation notes

`Stacks.ProjectiveFromSections.GeneratesStalks` is the stalkwise reading of generation — the
germs of the sections generate every stalk of `L` over the corresponding stalk of `𝒪_X` — and is
stated for a family indexed by an arbitrary type. `Generates` is therefore literally the case
where the index type is `V` itself and the family is `ψ`, with no basis and no finiteness
entering the statement.

That the hypothesis does not depend on the chosen family, only on its span, is
`generatesBy_of_mem_span`. Its proof is the one of
`Stacks.Bertini.FamilyDivisors.chartFunction_mem_span_image` transported to germs: the sections
whose germ at a point lies in `𝔪ₓ · Lₓ` form a `k`-submodule of `Γ(X, L)`, because `ψ` is
`k`-linear and a scalar of `k` acts through `Stacks.Bertini.baseRingHom`, so if every member of a
spanning family vanishes at a point then so does every section of the system; and for an
invertible module generation of the stalks is exactly the statement that the nonvanishing opens
cover `X` (`Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem`).

The step that connects the hypothesis to the chart equations needs only *one* inclusion between
the nonvanishing locus of a section and the support of its zero scheme, namely
`X_s ⊆ |Z(s)|ᶜ`. That inclusion is proved here from a local trivialization and needs nothing of
`X`: on an affine open where `L` is trivialized the ideal of `Z(s)` is generated by the function
representing `s` (`AlgebraicGeometry.zeroScheme_ideal_of_trivialization`), and at a point where
`s` does not vanish that function is a unit in the stalk. The *equality*
`X_s = |Z(s)|ᶜ` is `AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme`, which
carries hypotheses `[IsIntegral X]` and `s ≠ 0` because its other inclusion needs the section to
be regular; neither hypothesis is available in the situation of [Stacks, Tag 0FD6], and neither
is needed for the inclusion used here.

No `@[stacks]` attribute is attached: the hypotheses of [Stacks, Tag 0FD6] are not themselves
assertions of the tag, and the tag's carrier is its conclusion.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ModuleStalk Stacks.ProjectiveFromSections

universe u v

namespace AlgebraicGeometry

/-- **A section does not vanish at a point of its nonvanishing open, so that point is outside
the support of its zero scheme.** On an affine open where `L` is trivialized the ideal of `Z(s)`
is generated by the function `a` representing `s`, and `s = a · b` for `b` the frame; the germ of
`s` at the point avoids `𝔪ₓ · Lₓ`, so the germ of `a` is a unit and the point lies in the basic
open of `a`, which is the complement of the zero locus of that ideal.

Only this inclusion is proved, not the equality of `X_s` with the complement of `|Z(s)|`: the
reverse inclusion needs `s` to be a regular section, which on an integral scheme follows from
`s ≠ 0` and is `AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme`. -/
theorem notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) {x : X}
    (hx : x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L s) :
    x ∉ (zeroScheme X L s).supportSet := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  obtain ⟨g, hxg, -, ⟨e⟩⟩ := exists_basicOpen_linearEquiv L U x hxU
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem
      (U := ⟨X.basicOpen g, U.2.basicOpen g⟩) hxg,
    zeroScheme_ideal_of_trivialization X L s ⟨X.basicOpen g, U.2.basicOpen g⟩ e _ rfl,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not]
  set a : Γ(X, X.basicOpen g) := e (L.presheaf.map (homOfLE le_top).op s) with ha
  refine (X.mem_basicOpen a x hxg).mpr ?_
  have hsW : L.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op s = a • e.symm 1 := by
    rw [← map_smul e.symm a 1, smul_eq_mul, mul_one, ha, e.symm_apply_apply]
  have hgerm : (L.presheaf.Γgerm x).hom s =
      (X.presheaf.germ (X.basicOpen g) x hxg).hom a •
        (L.presheaf.germ (X.basicOpen g) x hxg).hom (e.symm 1) := by
    rw [← TopCat.Presheaf.Γgerm_res_apply
      (i := homOfLE (le_top : X.basicOpen g ≤ ⊤)) L.presheaf x hxg s, hsW,
      Stacks.ModuleStalk.germ_smul]
  rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, hgerm,
    smul_mem_maximalSmul_iff] at hx
  exact not_not.mp (not_or.mp hx).1

end AlgebraicGeometry

namespace Stacks.Bertini.FamilyDivisors

open Stacks.AmpleImmersionReduction Stacks.NonvanishingSpelling

/-- The invertibility of `L` in the spelling used by the generating-system machinery of
[Stacks, Tag 01ND] and [Stacks, Tag 0FCY]. The field `Stacks.Bertini.FamilyDivisors.isInvertible`
of the standing situation is the same statement with the sheaf condition on the structure
presheaf supplied differently, and instance search does not cross between the two spellings. -/
instance isInvertibleModule (D : FamilyDivisors.{u, v}) :
    Stacks.Ample.IsInvertibleModule D.X D.L :=
  D.isInvertible

variable (D : FamilyDivisors.{u, v})

/-! ### The generation hypothesis -/

/-- **The sections of a family of vectors of the linear system generate `L`**, stalkwise: the
germs of the `ψ(wⱼ)` generate every stalk of `L`. For a basis of `V` indexed by `Fin (n + 1)`
this is the hypothesis of the morphism `φ_{L,ψ} : X → 𝐏(V)` of [Stacks, Tag 0FCY]. -/
def GeneratesBy {ι : Type*} (v : ι → D.V) : Prop :=
  GeneratesStalks (fun i => D.sectionOf (v i))

/-- **Hypothesis (2) of [Stacks, Tag 0FD6]: the image of `ψ` generates `L`.** This is
`GeneratesBy` for the family of *all* vectors of the linear system, so it mentions neither a
basis nor the dimension of `V`; `generates_iff_generatesBy_basis` turns it into the hypothesis
at any chosen basis. -/
def Generates : Prop :=
  GeneratesStalks D.sectionOf

/-- The family `ψ(v₁), …, ψ(v_r)` of the sections of the chosen basis of the linear system. -/
def basisSections : Fin (Module.finrank D.k D.V) → Γ(D.L, ⊤) :=
  fun i => D.sectionOf (D.basis i)

/-- The image of `ψ` generates `L` if and only if the sections of the family of all vectors of
`V`, indexed by `V` itself, generate `L`. -/
theorem generates_iff_generatesBy_id : D.Generates ↔ D.GeneratesBy (id : D.V → D.V) :=
  Iff.rfl

/-- **Generation depends only on the span of the family.** If the sections of `v` generate `L`
and every `v i` lies in the `k`-span of `w`, then the sections of `w` generate `L`.

Vanishing at a point is a `k`-linear condition: the sections of `L` whose germ at `x` lies in
`𝔪ₓ · Lₓ` form a submodule over the stalk of the structure sheaf, hence over `k`, which acts
through `Stacks.Bertini.baseRingHom`. So if every `ψ(wⱼ)` vanished at `x` then so would every
`ψ(y)` for `y` in the span, in particular some `ψ(v i)` — and a generating family vanishes
nowhere simultaneously. -/
theorem generatesBy_of_mem_span {ι κ : Type*} {v : ι → D.V} {w : κ → D.V}
    (hv : D.GeneratesBy v) (hw : ∀ i, v i ∈ Submodule.span D.k (Set.range w)) :
    D.GeneratesBy w := by
  refine generatesStalks_of_forall_exists_mem _ fun x => ?_
  by_contra hx
  simp only [not_exists] at hx
  have hvanish : ∀ j, (D.L.presheaf.Γgerm x).hom (D.sectionOf (w j)) ∈ maximalSmul D.L x := by
    intro j
    have hj := hx j
    rwa [mem_nonvanishingOpen_iff, not_not] at hj
  have hsub : ∀ y ∈ Submodule.span D.k (Set.range w),
      (D.L.presheaf.Γgerm x).hom (D.sectionOf y) ∈ maximalSmul D.L x := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hvanish j
    | zero => rw [D.sectionOf_zero, map_zero]; exact Submodule.zero_mem _
    | add p q _ _ hp hq => rw [D.sectionOf_add, map_add]; exact Submodule.add_mem _ hp hq
    | smul c p _ hp =>
      rw [D.sectionOf_smul, Stacks.ModuleStalk.Γgerm_smul]
      exact Submodule.smul_mem _ _ hp
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks _ hv x
  rw [mem_nonvanishingOpen_iff] at hi
  exact hi (hsub (v i) (hw i))

/-- **Hypothesis (2) is generation by any spanning family of the linear system.** -/
theorem generates_iff_generatesBy_of_span_eq_top {ι : Type*} (v : ι → D.V)
    (hv : Submodule.span D.k (Set.range v) = ⊤) : D.Generates ↔ D.GeneratesBy v :=
  ⟨fun h => D.generatesBy_of_mem_span (v := id) h fun _ => hv ▸ Submodule.mem_top,
    fun h => D.generatesBy_of_mem_span (w := id) h fun _ => by
      rw [Set.range_id, Submodule.span_univ]; exact Submodule.mem_top⟩

/-- **Hypothesis (2) is generation by the sections of any basis of the linear system.** The
morphism to `𝐏(V)` of [Stacks, Tag 0FCY] is built from a basis indexed by `Fin (n + 1)`, while
the standing situation carries one indexed by `Fin (dim V)`; this is what lets the hypothesis be
stated once and used at either. -/
theorem generates_iff_generatesBy_basis {ι : Type*} (b : Module.Basis ι D.k D.V) :
    D.Generates ↔ D.GeneratesBy b :=
  D.generates_iff_generatesBy_of_span_eq_top _ b.span_eq

/-- **Hypothesis (2), handed to [Stacks, Tag 0FCY] at a chosen basis.** -/
theorem generatesBy_basis (h : D.Generates) {ι : Type*} (b : Module.Basis ι D.k D.V) :
    D.GeneratesBy b :=
  (D.generates_iff_generatesBy_basis b).mp h

/-- **Hypothesis (2) carried from one basis of the linear system to another.** The hypothesis is
basis free (`Stacks.Bertini.FamilyDivisors.generates_iff_generatesBy_basis`), so generation by
the sections of one basis gives generation by the sections of any other, at any index type. This
is what lets a consumer taking hypothesis (3) at one basis read it at another without carrying a
second generation hypothesis. -/
theorem generatesBy_basis_of_generatesBy {ι κ : Type*} {b : Module.Basis ι D.k D.V}
    (hb : D.GeneratesBy b) (b' : Module.Basis κ D.k D.V) : D.GeneratesBy b' :=
  D.generatesBy_basis ((D.generates_iff_generatesBy_basis b).mpr hb) b'

/-- **Hypothesis (2), as stalkwise generation by the sections of the chosen basis.** -/
theorem generatesStalks_basisSections (h : D.Generates) : GeneratesStalks D.basisSections :=
  D.generatesBy_basis h D.basis

/-! ### The common zero locus is empty -/

/-- **A point where some section of the linear system does not vanish is outside the divisor of
that section.** -/
theorem notMem_divisorSet_of_mem_nonvanishingOpen (w : D.V) {x : D.X}
    (hx : x ∈ Stacks.NonvanishingOpen.nonvanishingOpen D.X D.L (D.sectionOf w)) :
    x ∉ D.divisorSet w :=
  notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen D.L (D.sectionOf w) hx

/-- **Under hypothesis (2) the common zero locus `Z = ⋂_{v ∈ V} H_v` is empty.** This is the
geometric content of the hypothesis: a generating family has, at every point, a member not
vanishing there, and that member's divisor misses the point. -/
theorem commonZeroSet_eq_empty_of_generates (h : D.Generates) : D.commonZeroSet = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨i, hi⟩ :=
    exists_mem_nvCover_of_generatesStalks _ (D.generatesStalks_basisSections h) x
  exact D.notMem_divisorSet_of_mem_nonvanishingOpen (D.basis i) hi
    (D.commonZeroSet_subset_divisorSet (D.basis i) hx)

/-! ### The open of a rational point under the generation hypothesis -/

section RationalPoint

variable {D} {U : D.X.Opens}

/-- **Under hypothesis (2) some coefficient `cᵢ = fᵢ(x)` at a `k`-point of a trivializing chart
is nonzero.** This is
`Stacks.Bertini.FamilyDivisors.exists_rationalPointCoeff_ne_zero_of_notMem_commonZeroSet` with
its hypothesis discharged: the image of `ψ` generates `L`, so the common zero locus is empty and
*every* point of `X` lies outside it. -/
theorem exists_rationalPointCoeff_ne_zero_of_generates [IsAffine U.toScheme]
    (h : D.Generates)
    (eU : D.restrictedModule U ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (x₀ : Spec (.of D.k) ⟶ U.toScheme) (p : Spec (.of D.k)) :
    ∃ i, rationalPointCoeff eU x₀ i ≠ 0 :=
  exists_rationalPointCoeff_ne_zero_of_notMem_commonZeroSet eU x₀ p
    (by rw [D.commonZeroSet_eq_empty_of_generates h]; exact Set.notMem_empty _)

/-- **Under hypothesis (2) the open `D(∑ᵢ cᵢxᵢ) ⊂ 𝔸^r_k` of a `k`-point of a trivializing chart
is nonempty**, which is the form in which the parameter opens of the proof of [Stacks, Tag 0FD6]
are combined. -/
theorem nonempty_rationalPointOpen_of_generates [IsAffine U.toScheme]
    (h : D.Generates)
    (eU : D.restrictedModule U ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (x₀ : Spec (.of D.k) ⟶ U.toScheme) (p : Spec (.of D.k)) :
    ((rationalPointOpen eU x₀ : D.parameterBase.Opens) : Set D.parameterBase).Nonempty := by
  obtain ⟨i, hi⟩ := exists_rationalPointCoeff_ne_zero_of_generates h eU x₀ p
  exact nonempty_rationalPointOpen eU x₀ hi

end RationalPoint

end Stacks.Bertini.FamilyDivisors

end
