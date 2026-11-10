module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalKernelComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel

/-!
# Lifting a conormal class along a presentation that admits no factorisation back

Let `φ₂ : R₀[ι] ⟶ T` be a presentation of a commutative ring by a polynomial ring, let
`φ₁ : P₁ ⟶ T` be another presentation, and let `u : P₁ ⟶ R₀[ι]` be a factorisation of `φ₁`
through `φ₂` over the base `R₀`.  The comparison of the degree `-1` cohomology of the two
naive cotangent complexes asks for a factorisation in the other direction, which over a site
does not exist: a lift of a generator through a locally surjective presentation exists only
locally.

What is available is a lift of *finitely many* generators at a time, and that is enough,
because a conormal class is represented by a single polynomial `q`, which involves only
finitely many variables.  Truncating to those variables gives a third presentation
`R₀[q.vars] ⟶ T` which both of the others factor — by the inclusion `t` on one side and, once
the variables of `q` are lifted, by a substitution `σ` on the other — and the ring-level
degree `-1` comparison of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalKernelComparison.lean` applies to that
configuration.

## Main results

* `Stacks.Sites.Conormal.exists_mem_ker_sub_mem_sq_of_vars_lift`: **a conormal class of
  `φ₂` killed by its conormal map lifts to one of `φ₁` as soon as the variables of a
  representative lift.**  The witness is `σ q`, it again lies in the kernel of its own
  conormal map, and its image under `u` agrees with `q` modulo the square of the kernel of
  `φ₂`, which is to say that the two conormal classes correspond.
* `Stacks.Sites.Conormal.exists_finset_rename_forall_rename_pderiv_mem`: the truncation
  itself, that a polynomial all of whose partial derivatives lie in an ideal comes from the
  polynomial ring on its own variables, with all partial derivatives there still landing in
  the ideal.

## Implementation notes

The three conclusions are exactly the data a conormal class in the kernel of the conormal map
consists of — membership in the kernel ideal, vanishing of the universal differential, and the
comparison modulo the square — and no second-order Taylor expansion appears in the proof: the
homotopy identity of Stacks 00S1 (2) in degree `-1` already expresses the difference of
two factorisations modulo the square of the kernel.

The algebra structure on `R₀[ι]` is the one induced by `MvPolynomial.C`, which is *not*
definitionally the standard one; that is why the derivative criterion is quoted in the form
`KaehlerDifferential.one_tmul_D_eq_zero_iff_pderiv_mem`, which takes the structural map as a
hypothesis.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the homotopy
  behind the comparison.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of
  the naive cotangent complex from the presentation, whose degree `-1` comparison this serves.
-/

@[expose] public section

open CategoryTheory TensorProduct

universe w

namespace Stacks.Sites.Conormal

section Truncation

variable {R₀ : Type*} [CommRing R₀] {ι : Type*}

/-- **Truncation to the variables of one polynomial.**  A polynomial is the image, under the
inclusion of the polynomial ring on its own variables, of a polynomial there; and if all of
its partial derivatives lie in an ideal `I` then so do the images of all the partial
derivatives of that polynomial. -/
theorem exists_finset_rename_forall_rename_pderiv_mem (I : Ideal (MvPolynomial ι R₀))
    (q : MvPolynomial ι R₀) (hq : ∀ i, MvPolynomial.pderiv i q ∈ I) :
    ∃ p : MvPolynomial {x // x ∈ q.vars} R₀,
      MvPolynomial.rename (Subtype.val : {x // x ∈ q.vars} → ι) p = q ∧
        ∀ j : {x // x ∈ q.vars}, MvPolynomial.rename (Subtype.val : {x // x ∈ q.vars} → ι)
          (MvPolynomial.pderiv j p) ∈ I := by
  obtain ⟨p, hp⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q
    (Subtype.val : {x // x ∈ q.vars} → ι) Subtype.val_injective (by simp)
  refine ⟨p, hp, fun j ↦ ?_⟩
  rw [← MvPolynomial.pderiv_rename Subtype.val_injective, hp]
  exact hq _

end Truncation

section Substitution

variable {R₀ T P₁ : CommRingCat.{w}} {ι : Type w}
  (φ₂ : CommRingCat.of (MvPolynomial ι R₀) ⟶ T) (φ₁ : P₁ ⟶ T)
  (u : P₁ ⟶ CommRingCat.of (MvPolynomial ι R₀)) (b₁ : R₀ ⟶ P₁)
  (hu : u ≫ φ₂ = φ₁)
  (hb : b₁ ≫ u = CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := R₀)))

include hu hb in
/-- **A conormal class in the kernel of the conormal map lifts along a factorisation as soon
as the variables of a representative lift.**  Let `q` lie in the kernel of a polynomial
presentation `φ₂` and have all of its partial derivatives there, that is let its conormal
class be killed by the conormal map, and let every variable occurring in `q` have its image
in `T` lifted through a second presentation `φ₁` which factors through `φ₂` by `u` over the
base.  Then the kernel of `φ₁` contains an element `p` whose universal differential vanishes
and whose image under `u` is `q` modulo the square of the kernel of `φ₂`: the conormal class
of `q` is the image of the conormal class of `p`.

The element `p` is the substitution of the chosen lifts into the truncation of `q` to the
polynomial ring on its own variables, and that truncation is what makes finitely many lifts
suffice. -/
theorem exists_mem_ker_sub_mem_sq_of_vars_lift
    (q : MvPolynomial ι R₀) (hq : q ∈ RingHom.ker φ₂.hom)
    (hpd : ∀ i, MvPolynomial.pderiv i q ∈ RingHom.ker φ₂.hom)
    (hlift : ∀ i ∈ q.vars, ∃ c : P₁, φ₁.hom c = φ₂.hom (MvPolynomial.X i)) :
    ∃ p : P₁, p ∈ RingHom.ker φ₁.hom ∧
      (1 : P₁ ⧸ RingHom.ker φ₁.hom) ⊗ₜ[P₁]
          CommRingCat.KaehlerDifferential.d (f := b₁) p = 0 ∧
        u.hom p - q ∈ RingHom.ker φ₂.hom ^ 2 := by
  classical
  obtain ⟨p₀, hp₀, hpd₀⟩ :=
    exists_finset_rename_forall_rename_pderiv_mem (RingHom.ker φ₂.hom) q hpd
  choose c hc using fun j : {x // x ∈ q.vars} ↦ hlift j.1 j.2
  let : Algebra R₀ P₁ := b₁.hom.toAlgebra
  set Pr : CommRingCat.{w} := CommRingCat.of (MvPolynomial {x // x ∈ q.vars} R₀)
  set t : Pr ⟶ CommRingCat.of (MvPolynomial ι R₀) :=
    CommRingCat.ofHom (MvPolynomial.rename
      (Subtype.val : {x // x ∈ q.vars} → ι)).toRingHom
  set σ : Pr ⟶ P₁ := CommRingCat.ofHom (MvPolynomial.aeval c).toRingHom
  set b : R₀ ⟶ Pr := CommRingCat.ofHom MvPolynomial.C
  set b₂ : R₀ ⟶ CommRingCat.of (MvPolynomial ι R₀) :=
    CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := R₀))
  set φ : Pr ⟶ T := t ≫ φ₂ with hφ'
  -- the substitution is a factorisation of the truncation through `φ₁`
  have hσ : σ ≫ φ₁ = φ := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      change φ₁.hom (MvPolynomial.aeval c (MvPolynomial.C r)) =
        φ₂.hom (MvPolynomial.rename Subtype.val (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.rename_C]
      have key : b₁ ≫ φ₁ = b₂ ≫ φ₂ := by rw [← hu, ← Category.assoc, hb]
      exact congrArg (fun f : R₀ ⟶ T ↦ f.hom r) key
    · intro j
      change φ₁.hom (MvPolynomial.aeval c (MvPolynomial.X j)) =
        φ₂.hom (MvPolynomial.rename Subtype.val (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X, MvPolynomial.rename_X]
      exact hc j
  have hbσ : b ≫ σ = b₁ := CommRingCat.hom_ext (RingHom.ext (MvPolynomial.aeval_C c))
  have hbt : b ≫ t = b₂ := CommRingCat.hom_ext (RingHom.ext (MvPolynomial.rename_C _))
  -- the truncation lies in the kernel and its universal differential vanishes
  have hq₀ : p₀ ∈ RingHom.ker φ.hom := by
    change φ₂.hom (MvPolynomial.rename Subtype.val p₀) = 0
    rw [hp₀]
    exact hq
  have hd₀ : (1 : Pr ⧸ RingHom.ker φ.hom) ⊗ₜ[Pr]
      CommRingCat.KaehlerDifferential.d (f := b) p₀ = 0 :=
    (KaehlerDifferential.one_tmul_D_eq_zero_iff_pderiv_mem (inst := b.hom.toAlgebra)
      (fun _ ↦ rfl) (RingHom.ker φ.hom) p₀).mpr hpd₀
  refine ⟨σ.hom p₀, mem_ker_of_fac φ φ₁ σ hσ hq₀,
    one_tmul_d_eq_zero_of_fac φ φ₁ σ hσ b b₁ hbσ p₀ hq₀ hd₀, ?_⟩
  have hsub := sub_mem_sq_of_substitution φ φ₁ φ₂ u σ t hu hσ rfl b b₁ b₂ hbσ hb hbt p₀ hq₀ hd₀
  rwa [show t.hom p₀ = q from hp₀] at hsub

end Substitution

end Stacks.Sites.Conormal

end
