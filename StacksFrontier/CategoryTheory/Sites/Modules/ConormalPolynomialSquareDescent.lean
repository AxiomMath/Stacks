module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialSubstitution
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialSquareTruncation

/-!
# Descending a square membership along a presentation that admits no factorisation back

Let `φ₁ : R₀[ι] ⟶ T₀` and `φ₂ : R₀[κ] ⟶ T₀` be two presentations of a commutative ring by
polynomial rings over `R₀` and let `u : R₀[ι] ⟶ R₀[κ]` be a factorisation of `φ₁` through
`φ₂` over `R₀`.  The degree `-1` comparison of the two naive cotangent complexes asks, in its
injective direction, for the converse of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalPolynomialSubstitution.lean`: an element `q`
of the kernel of `φ₁` whose conormal class is killed by the conormal map and whose image under
`u` lies in the square of the kernel of `φ₂` should already lie in the square of the kernel of
`φ₁`.

That needs a factorisation of `φ₂` back through `φ₁`, which over a site does not exist: a lift
of a generator through a locally surjective presentation exists only locally.  What is
available is a lift of *finitely many* generators at a time, and that is enough, because the
witness of the square membership of `u q` involves only finitely many variables of `κ`.  The
two results below are the two halves of that argument, split at exactly the point where a site
has to interpose a covering: the first produces the finite set of variables, the second
consumes a lift of each of them.

Because the lift of a variable exists only after restriction to a covering object, the second
result is stated for a further ring `P` with a map `res : R₀[ι] ⟶ P` over `R₀` carrying `φ₁`
to a presentation `ψ : P ⟶ T₁` of a localised target, and concludes about `res q` rather than
about `q`: restriction is what the covering adds, and it appears in the statement rather than
being bolted on afterwards.

## Main results

* `Stacks.Sites.Conormal.exists_finset_rename_mem_ker_sq_vars_subset`: the finite set of
  variables.  A member of the square of the kernel of `φ₂` which is the `u`-image of `q` comes
  from the polynomial ring on a finite set of variables of `κ` which also contains every
  variable occurring in `u` of a variable of `q`.
* `Stacks.Sites.Conormal.mem_ker_sq_of_rename_lift`: **the descent.**  Once the images in `T₀`
  of the finitely many variables of that set lift through `ψ`, the restriction of `q` lies in
  the square of the kernel of `ψ`.

## Implementation notes

The two factorisations fed to `Stacks.Sites.Conormal.sub_mem_sq_of_one_tmul_d_eq_zero` are both
defined on the polynomial ring on the variables of `q`: the inclusion followed by `res`, and
the substitution of the chosen lifts into the truncated witness.  Their difference is therefore
controlled by the homotopy of Stacks 00S1 (2) in degree `-1`, and no second-order Taylor
expansion appears; the hypothesis that all partial derivatives of `q` lie in the kernel is what
feeds that homotopy, and it is the statement that the conormal class of `q` is killed by the
conormal map.

The substitution is read off from the witness, not from `q`: the finite set is the one the
truncation of the witness returns, enlarged so that the image under `u` of every variable of
`q` is a polynomial in it.  That is why the first result prescribes the enlargement — the
truncation of `StacksFrontier/CategoryTheory/Sites/Modules/PolynomialSquareTruncation.lean`
accepts any prescribed finite set.

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

section SquareDescent

/-- A member of the square of an ideal lies in the square of any larger ideal. -/
private theorem mem_sq_of_le {R : Type*} [CommRing R] {I K : Ideal R} (h : I ≤ K) {z : R}
    (hz : z ∈ I ^ 2) : z ∈ K ^ 2 := by
  rw [pow_two] at hz ⊢
  exact Ideal.mul_mono h h hz

/-- An element sent into the kernel of `φ` by `t` lies in the kernel of `t ≫ φ ≫ ρ`. -/
private theorem mem_ker_comp_comp_of_map_mem_ker {A B C D : CommRingCat.{w}} (t : A ⟶ B)
    (φ : B ⟶ C) (ρ : C ⟶ D) {x : A} (hx : t.hom x ∈ RingHom.ker φ.hom) :
    x ∈ RingHom.ker (t ≫ φ ≫ ρ).hom := by
  change ρ.hom (φ.hom (t.hom x)) = 0
  rw [RingHom.mem_ker.mp hx, map_zero]

variable {R₀ T₀ T₁ P : CommRingCat.{w}} {ι κ : Type w}

/-- **The finite set of variables of the descent.**  If the image under a factorisation `u` of
an element `q` lies in the square of the kernel of a polynomial presentation `φ₂`, then it is
the image of a member of the square of the kernel of the presentation truncated to a finite set
of variables, and that finite set may be taken to contain every variable occurring in the image
under `u` of a variable of `q`. -/
theorem exists_finset_rename_mem_ker_sq_vars_subset
    (φ₂ : CommRingCat.of (MvPolynomial κ R₀) ⟶ T₀)
    (u : CommRingCat.of (MvPolynomial ι R₀) ⟶ CommRingCat.of (MvPolynomial κ R₀))
    (q : MvPolynomial ι R₀) (hsq : u.hom q ∈ RingHom.ker φ₂.hom ^ 2) :
    ∃ (s : Finset κ) (p : MvPolynomial {j // j ∈ s} R₀),
      (∀ x ∈ q.vars, (u.hom (MvPolynomial.X x)).vars ⊆ s) ∧
        MvPolynomial.rename (Subtype.val : {j // j ∈ s} → κ) p = u.hom q ∧
          p ∈ RingHom.ker (φ₂.hom.comp (MvPolynomial.rename
            (Subtype.val : {j // j ∈ s} → κ)).toRingHom) ^ 2 := by
  classical
  obtain ⟨s, hs, p, hp, hpsq⟩ := exists_finset_rename_mem_ker_sq φ₂.hom
    (q.vars.biUnion fun x ↦ (u.hom (MvPolynomial.X x)).vars) (u.hom q) hsq
  exact ⟨s, p, fun x hx ↦ (Finset.subset_biUnion_of_mem _ hx).trans hs, hp, hpsq⟩

variable (φ₁ : CommRingCat.of (MvPolynomial ι R₀) ⟶ T₀)
  (φ₂ : CommRingCat.of (MvPolynomial κ R₀) ⟶ T₀)
  (u : CommRingCat.of (MvPolynomial ι R₀) ⟶ CommRingCat.of (MvPolynomial κ R₀))
  (ψ : P ⟶ T₁) (ρ : T₀ ⟶ T₁)
  (res : CommRingCat.of (MvPolynomial ι R₀) ⟶ P) (bP : R₀ ⟶ P)
  (hu : u ≫ φ₂ = φ₁)
  (hbu : CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := R₀)) ≫ u =
    CommRingCat.ofHom (MvPolynomial.C (σ := κ) (R := R₀)))
  (hres : res ≫ ψ = φ₁ ≫ ρ)
  (hbres : CommRingCat.ofHom (MvPolynomial.C (σ := ι) (R := R₀)) ≫ res = bP)

include hu hbu hres hbres in
/-- The base map of `P` followed by `ψ` is the base map of `R₀[κ]` followed by `φ₂` and `ρ`. -/
theorem comp_eq_ofHom_C_comp_of_fac :
    bP ≫ ψ = CommRingCat.ofHom (MvPolynomial.C (σ := κ) (R := R₀)) ≫ φ₂ ≫ ρ := by
  rw [← hbres, Category.assoc, hres, ← hu]
  simp only [← Category.assoc]
  rw [hbu]

include hu hbu hres hbres in
/-- Substituting lifts through `ψ` of the images of the variables of `s` is a factorisation
through `ψ` of the presentation truncated to `s`. -/
theorem ofHom_eval₂Hom_comp_eq_of_lift {s : Finset κ} (c : {j // j ∈ s} → P)
    (hc : ∀ j, ψ.hom (c j) = ρ.hom (φ₂.hom (MvPolynomial.X j.1))) :
    CommRingCat.ofHom (MvPolynomial.eval₂Hom bP.hom c) ≫ ψ =
      CommRingCat.ofHom (MvPolynomial.rename (Subtype.val : {j // j ∈ s} → κ)).toRingHom ≫
        φ₂ ≫ ρ := by
  refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun j ↦ ?_)
  · change ψ.hom (MvPolynomial.eval₂Hom bP.hom c (MvPolynomial.C r)) =
      ρ.hom (φ₂.hom (MvPolynomial.rename Subtype.val (MvPolynomial.C r)))
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.rename_C]
    exact congrArg (fun t : R₀ ⟶ T₁ ↦ t.hom r)
      (comp_eq_ofHom_C_comp_of_fac φ₁ φ₂ u ψ ρ res bP hu hbu hres hbres)
  · change ψ.hom (MvPolynomial.eval₂Hom bP.hom c (MvPolynomial.X j)) =
      ρ.hom (φ₂.hom (MvPolynomial.rename Subtype.val (MvPolynomial.X j)))
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.rename_X]
    exact hc j

include hbu in
/-- A substitution `g` of polynomials for variables represents `u` on renamed polynomials as
soon as it does so on each variable. -/
theorem ofHom_aeval_comp_rename_eq {ι' κ' : Type w} (e : ι' → ι) (f : κ' → κ)
    (g : ι' → MvPolynomial κ' R₀)
    (hg : ∀ x, MvPolynomial.rename f (g x) = u.hom (MvPolynomial.X (e x))) :
    CommRingCat.ofHom (MvPolynomial.aeval g).toRingHom ≫
        CommRingCat.ofHom (MvPolynomial.rename f).toRingHom =
      CommRingCat.ofHom (MvPolynomial.rename e).toRingHom ≫ u := by
  refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun x ↦ ?_)
  · change MvPolynomial.rename f (MvPolynomial.aeval g (MvPolynomial.C r)) =
      u.hom (MvPolynomial.rename e (MvPolynomial.C r))
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.rename_C,
      MvPolynomial.rename_C]
    exact (congrArg (fun t : R₀ ⟶ CommRingCat.of (MvPolynomial κ R₀) ↦ t.hom r) hbu).symm
  · change MvPolynomial.rename f (MvPolynomial.aeval g (MvPolynomial.X x)) =
      u.hom (MvPolynomial.rename e (MvPolynomial.X x))
    rw [MvPolynomial.aeval_X, MvPolynomial.rename_X]
    exact hg x

include hres hbres in
/-- A factorisation `v` over the base of a renamed presentation through `ψ` agrees with `res`,
modulo the square of the kernel of `ψ`, on a polynomial whose renaming and whose renamed partial
derivatives lie in the kernel of `φ₁`. -/
theorem sub_mem_ker_sq_of_rename {ι' : Type w} (e : ι' → ι)
    (v : CommRingCat.of (MvPolynomial ι' R₀) ⟶ P)
    (hv : v ≫ ψ = CommRingCat.ofHom (MvPolynomial.rename e).toRingHom ≫ φ₁ ≫ ρ)
    (hbv : CommRingCat.ofHom MvPolynomial.C ≫ v = bP) (p₀ : MvPolynomial ι' R₀)
    (hq : MvPolynomial.rename e p₀ ∈ RingHom.ker φ₁.hom)
    (hpd : ∀ j, MvPolynomial.rename e (MvPolynomial.pderiv j p₀) ∈ RingHom.ker φ₁.hom) :
    res.hom (MvPolynomial.rename e p₀) - v.hom p₀ ∈ RingHom.ker ψ.hom ^ 2 := by
  let tr : CommRingCat.of (MvPolynomial ι' R₀) ⟶ CommRingCat.of (MvPolynomial ι R₀) :=
    CommRingCat.ofHom (MvPolynomial.rename e).toRingHom
  let b : R₀ ⟶ CommRingCat.of (MvPolynomial ι' R₀) := CommRingCat.ofHom MvPolynomial.C
  let φPr : CommRingCat.of (MvPolynomial ι' R₀) ⟶ T₁ := tr ≫ φ₁ ≫ ρ
  have hbt : b ≫ tr ≫ res = bP := by
    rw [← Category.assoc, ← hbres]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r ↦ MvPolynomial.rename_C e r)
  exact sub_mem_sq_of_one_tmul_d_eq_zero φPr ψ (tr ≫ res) v (by rw [Category.assoc, hres]) hv
    b bP hbt hbv p₀ (mem_ker_comp_comp_of_map_mem_ker tr φ₁ ρ hq)
    ((KaehlerDifferential.one_tmul_D_eq_zero_iff_pderiv_mem
      (inst := b.hom.toAlgebra) (fun _ ↦ rfl) (RingHom.ker φPr.hom) p₀).mpr
      fun j ↦ mem_ker_comp_comp_of_map_mem_ker tr φ₁ ρ (hpd j))

include hu hbu hres hbres in
/-- **The descent of a square membership along a factorisation.**  Let `q` lie in the kernel of
a polynomial presentation `φ₁` and have all of its partial derivatives there, that is let its
conormal class be killed by the conormal map, and let `u` be a factorisation of `φ₁` through a
second polynomial presentation `φ₂` over the base.  Let the image `u q` come, as a member of
the square of the kernel of `φ₂`, from the polynomial ring on a finite set `s` of variables
large enough to contain the variables of the image under `u` of every variable of `q`, and let
the image in `T₀` of every variable of `s` lift through a presentation `ψ` which `φ₁` maps to.
Then the image of `q` lies in the square of the kernel of `ψ`.

The two factorisations of the truncation of `q` to its own variables through `ψ` — the
inclusion followed by the comparison map, and the substitution of the chosen lifts into the
truncated witness — differ, by the homotopy of Stacks 00S1 (2) in degree `-1`, by a member of
the square of the kernel of `ψ`; and the second of them is itself such a member, being the
image of one along a factorisation. -/
theorem mem_ker_sq_of_rename_lift
    (q : MvPolynomial ι R₀) (hq : q ∈ RingHom.ker φ₁.hom)
    (hpd : ∀ i, MvPolynomial.pderiv i q ∈ RingHom.ker φ₁.hom)
    (s : Finset κ) (p : MvPolynomial {j // j ∈ s} R₀)
    (hvars : ∀ x ∈ q.vars, (u.hom (MvPolynomial.X x)).vars ⊆ s)
    (hp : MvPolynomial.rename (Subtype.val : {j // j ∈ s} → κ) p = u.hom q)
    (hpsq : p ∈ RingHom.ker (φ₂.hom.comp (MvPolynomial.rename
      (Subtype.val : {j // j ∈ s} → κ)).toRingHom) ^ 2)
    (hlift : ∀ j ∈ s, ∃ c : P, ψ.hom c = ρ.hom (φ₂.hom (MvPolynomial.X j))) :
    res.hom q ∈ RingHom.ker ψ.hom ^ 2 := by
  classical
  obtain ⟨p₀, hp₀, hpd₀⟩ :=
    exists_finset_rename_forall_rename_pderiv_mem (RingHom.ker φ₁.hom) q hpd
  choose c hc using fun j : {j // j ∈ s} ↦ hlift j.1 j.2
  choose g hg using fun x : {x // x ∈ q.vars} ↦
    MvPolynomial.exists_rename_eq_of_vars_subset_range (u.hom (MvPolynomial.X x.1))
      (Subtype.val : {j // j ∈ s} → κ) Subtype.val_injective
      (fun i hi ↦ ⟨⟨i, hvars x.1 x.2 (Finset.mem_coe.mp hi)⟩, rfl⟩)
  set σ : CommRingCat.of (MvPolynomial {j // j ∈ s} R₀) ⟶ P :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom bP.hom c)
  set j₀ : CommRingCat.of (MvPolynomial {x // x ∈ q.vars} R₀) ⟶
      CommRingCat.of (MvPolynomial {j // j ∈ s} R₀) :=
    CommRingCat.ofHom (MvPolynomial.aeval g).toRingHom
  have hσ := ofHom_eval₂Hom_comp_eq_of_lift φ₁ φ₂ u ψ ρ res bP hu hbu hres hbres c hc
  have hj₀ := ofHom_aeval_comp_rename_eq u hbu Subtype.val Subtype.val g hg
  have hbv : CommRingCat.ofHom MvPolynomial.C ≫ j₀ ≫ σ = bP :=
    CommRingCat.hom_ext (RingHom.ext fun r ↦ by
      change MvPolynomial.eval₂Hom bP.hom c (MvPolynomial.aeval g (MvPolynomial.C r)) = bP.hom r
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C])
  have hdiff := sub_mem_ker_sq_of_rename φ₁ ψ ρ res bP hres hbres Subtype.val (j₀ ≫ σ)
    (by rw [Category.assoc, hσ, reassoc_of% hj₀, reassoc_of% hu]) hbv p₀ (hp₀.symm ▸ hq) hpd₀
  have hj₀p : j₀.hom p₀ = p := by
    refine MvPolynomial.rename_injective _ Subtype.val_injective ?_
    have h : MvPolynomial.rename Subtype.val (j₀.hom p₀) =
        u.hom (MvPolynomial.rename Subtype.val p₀) :=
      congrArg (fun t ↦ t.hom p₀) hj₀
    rw [h, hp₀, hp]
  rw [show (j₀ ≫ σ).hom p₀ = σ.hom p from congrArg σ.hom hj₀p, hp₀] at hdiff
  have hpsq' : p ∈ RingHom.ker (CommRingCat.ofHom (MvPolynomial.rename
      (Subtype.val : {j // j ∈ s} → κ)).toRingHom ≫ φ₂ ≫ ρ).hom ^ 2 :=
    mem_sq_of_le (fun _ hx ↦ mem_ker_comp_comp_of_map_mem_ker _ φ₂ ρ hx) hpsq
  rw [← sub_add_cancel (res.hom q) (σ.hom p)]
  exact Ideal.add_mem _ hdiff (map_mem_ker_sq_of_fac _ ψ σ hσ hpsq')

end SquareDescent

end Stacks.Sites.Conormal

end
