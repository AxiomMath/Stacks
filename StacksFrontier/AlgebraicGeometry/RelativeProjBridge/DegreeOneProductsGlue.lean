module

public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.DegreeOneProducts

/-!
# Ring maps out of the chart at a degree-one section are determined by the degree-one ratios

`StacksFrontier/AlgebraicGeometry/RelativeProjBridge/DegreeOneProducts.lean` shows that, when the
section ring of a sheaf of graded algebras is generated in degree one, every homogeneous section
of degree `d` is a sum of products of `d` degree-one sections
(`…SheafGradedAlgebra.mem_prodClosure_of_adjoin_eq_top`). This file transports that along
`HomogeneousLocalization.Away.mk`. It is a separate module because it needs
`StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic`, which is not added to
`DegreeOneProducts.lean` itself.

## Main definitions

* `…SheafGradedAlgebra.awayAgree`: the degree-`k` sections on which two ring homomorphisms out of
  the chart ring at a degree-one section agree.

## Main results

* `…SheafGradedAlgebra.away_ringHom_ext_degree_one`: two ring homomorphisms out of
  `HomogeneousLocalization.Away (A.grading U) t`, for `t` a degree-one section, that agree on the
  ratios `m / t` of degree-one sections are equal. This is
  `Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` — which tests *all* the fractions `p / tᵏ` —
  refined to the degree-one numerators by `…SheafGradedAlgebra.mem_prodClosure_of_adjoin_eq_top`,
  and it is the finiteness-free counterpart of Mathlib's
  `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`.

Here `…` abbreviates `Stacks.AlgebraicGeometry.RelativeProjBridge`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open DirectSum

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-! ### Extensionality of ring maps out of the chart at a degree-one section -/

/-- The degree-`k` sections on which two ring homomorphisms out of the chart ring at a degree-one
section `t` agree, as an additive subgroup of the section ring: the sections `p` of degree `k`
with `φ (p / tᵏ) = ψ (p / tᵏ)`.

It is an additive subgroup because `Stacks.ProjGlobalSectionsAppTop.away_mk_zero`, `…away_mk_add`
and `…away_mk_neg` say that the fraction with a fixed power of `t` as denominator is additive in
its numerator, and that is what lets `prodClosure` — an `AddSubgroup.closure` — be compared
against it. -/
noncomputable def awayAgree {P : Type*} [CommRing P] {t : A.sectionRing U}
    (ht : t ∈ A.grading U 1)
    (φ ψ : HomogeneousLocalization.Away (A.grading U) t →+* P) (k : ℕ) :
    AddSubgroup (A.sectionRing U) where
  carrier := {p | ∃ hp : p ∈ A.grading U (k • 1),
    φ (HomogeneousLocalization.Away.mk (A.grading U) ht k p hp) =
      ψ (HomogeneousLocalization.Away.mk (A.grading U) ht k p hp)}
  zero_mem' := ⟨zero_mem _, by
    rw [Stacks.ProjGlobalSectionsAppTop.away_mk_zero (A.grading U) ht k, map_zero, map_zero]⟩
  add_mem' := by
    rintro p p' ⟨hp, hep⟩ ⟨hp', hep'⟩
    refine ⟨add_mem hp hp', ?_⟩
    rw [Stacks.ProjGlobalSectionsAppTop.away_mk_add (A.grading U) ht k hp hp', map_add, map_add,
      hep, hep']
  neg_mem' := by
    rintro p ⟨hp, hep⟩
    refine ⟨neg_mem hp, ?_⟩
    rw [Stacks.ProjGlobalSectionsAppTop.away_mk_neg (A.grading U) ht k hp, map_neg, map_neg, hep]

/-- Two ring homomorphisms out of the chart ring `HomogeneousLocalization.Away (A.grading U) t` at
a degree-one section `t` of a section ring generated in degree one are equal as soon as they agree
on the ratios `m / t` of degree-one sections.

`Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` is the same statement with *all* the fractions
`p / tᵏ` tested; this refines it to the degree-one numerators, and the hypothesis that makes the
refinement possible is degree-one generation of the section ring, in the `Algebra.adjoin` form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.adjoin_grading_one_eq_top`
produces over an affine open.

Mathlib's `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` is the corresponding
generation statement for the `Away` ring, but only for a *finite* family of generators, which the
degree-one part `Γ(V, ℰ)` of the symmetric algebra of a quasi-coherent module does not provide.
The finiteness-free replacement is `mem_prodClosure_of_adjoin_eq_top` above: a degree-`k` section
is a sum of products of `k` degree-one sections with a degree-zero coefficient. Transporting that
along `HomogeneousLocalization.Away.mk` is the whole proof — the fraction is additive in its
numerator (`awayAgree`) and `(a · m₁ ⋯ m_k) / tᵏ = (a / 1) · (m₁ / t) ⋯ (m_k / t)`
(`Stacks.ProjGlobalSectionsAppTop.away_mk_mul`).

**No hypothesis in degree zero is needed.** A degree-zero coefficient contributes the fraction
`a / 1`, which is itself a degree-one ratio: `a / 1 = (a · t) / t` with `a · t` of degree one
(`Stacks.ProjGlobalSectionsAppTop.away_mk_zero_eq_mk_one`). So the degree-one ratios alone
generate the chart ring.

**Stated at the section-ring spelling, not for an abstract `𝒜 : ℕ → σ` with `[GradedRing 𝒜]`.**
That is where the consumer `Γ(V, Sym ℰ)` meets it, and the generation input only exists there:
the transparency note of `StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing` measures
the synthesis of `SetLike.GradedMul` over a section ring as prohibitive, which is why
`prodClosure` and `mem_prodClosure_of_adjoin_eq_top` are written at this spelling in the first
place and why an abstract version instantiated here would not elaborate. -/
theorem away_ringHom_ext_degree_one {P : Type*} [CommRing P]
    (hgen : Algebra.adjoin (A.grading U 0) (A.grading U 1 : Set (A.sectionRing U)) = ⊤)
    {t : A.sectionRing U} (ht : t ∈ A.grading U 1)
    {φ ψ : HomogeneousLocalization.Away (A.grading U) t →+* P}
    (h1 : ∀ (m : A.sectionRing U) (hm : m ∈ A.grading U 1),
      φ (HomogeneousLocalization.Away.mk (A.grading U) ht 1 m hm) =
        ψ (HomogeneousLocalization.Away.mk (A.grading U) ht 1 m hm)) :
    φ = ψ := by
  have key : ∀ k : ℕ, prodClosure A U k ≤ awayAgree A U ht φ ψ k := by
    intro k
    induction k with
    | zero =>
        rw [prodClosure_zero]
        intro a ha
        have hat : a * t ∈ A.grading U 1 :=
          mul_mem_grading' A U (show 0 + 1 = 1 from rfl) ha ht
        refine ⟨ha, ?_⟩
        rw [Stacks.ProjGlobalSectionsAppTop.away_mk_zero_eq_mk_one (A.grading U) ht ha hat]
        exact h1 (a * t) hat
    | succ k ih =>
        rw [prodClosure_succ, AddSubgroup.closure_le]
        rintro z ⟨y, hy, x, hx, rfl⟩
        obtain ⟨hyk, hey⟩ := ih hy
        have hpp : y * x ∈ A.grading U ((k + 1) • 1) :=
          mul_mem_grading' A U (by simp) hyk hx
        refine ⟨hpp, ?_⟩
        rw [Stacks.ProjGlobalSectionsAppTop.away_mk_mul (A.grading U) ht k 1 hyk hx hpp,
          map_mul, map_mul, hey, h1 x hx]
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext (A.grading U) ht fun k p hp => ?_
  obtain ⟨y, hpy⟩ := (mem_grading_iff A U p).1 hp
  have h2 : p ∈ prodClosure A U (k • 1) := by
    rw [← hpy]; exact mem_prodClosure_of_adjoin_eq_top A U hgen (k • 1) y
  have hk : k • (1 : ℕ) = k := by simp
  rw [hk] at h2
  obtain ⟨_, heq⟩ := key k h2
  exact heq

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
