module

public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialSquareTruncation
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialSubstitution

/-!
# Descending a conormal boundary along a restriction of two polynomial presentations

Let `φ₁ : R₀[ι₁] ⟶ T₀` and `φ₂ : R₀[ι₂] ⟶ T₀` be two polynomial presentations of one ring,
let `u : R₀[ι₁] ⟶ R₀[ι₂]` be the substitution of variables attached to a map `h₁ : ι₁ → ι₂`
factoring the first through the second, and let `φ₁' : R₀'[ι₁'] ⟶ T` be the first presentation
read over a covering object, with coefficients restricted by `rr : R₀ ⟶ R₀'`, variables
relabelled by `e₁ : ι₁ → ι₁'` and target changed by `τ : T₀ ⟶ T`.

A conormal class of `φ₁` killed by the conormal map is represented by a polynomial `q` lying,
together with all of its partial derivatives, in `Ker φ₁`.  Suppose its image `u q` is a
conormal boundary for `φ₂`, that is lies in `(Ker φ₂)²`.  The injectivity half of Stacks 08TY
in degree `-1` asks that the class of `q` itself be a boundary — and that is false over the
base object: the argument needs lifts through `φ₁'` of the images in `T` of finitely many
variables of the second presentation, and on a site such lifts exist only after passing to a
covering.

The statement below is therefore ordered the way a site forces: it produces the finite set `s`
of variables of `φ₂` *first*, and only then consumes the lifts of those variables.  Everything
between is commutative algebra at one place.

## Main results

* `Stacks.Sites.Conormal.exists_finset_restriction_mem_ker_sq`: **a conormal class of the first
  presentation whose image is a boundary for the second is itself a boundary, after a
  restriction over which finitely many variables of the second presentation lift.**  The finite
  set of variables is produced before the lifts are given, which is what makes the statement
  usable on a site.

## Implementation notes

The two truncations are the content: `q` is pushed down to the polynomial ring on its own
variables by
`Stacks.Sites.Conormal.exists_finset_rename_forall_rename_pderiv_mem`, and the witness of
`u q ∈ (Ker φ₂)²` to the polynomial ring on a finite set `s` of variables containing the image
of the variables of `q` by `Stacks.Sites.Conormal.exists_finset_rename_mem_ker_sq`.  That `s`
is the finite set the statement produces.  Once the lifts are given, the three presentations
`R₀[q.vars] ⟶ T`, `R₀[s] ⟶ T` and `φ₁'` are related by a triangle of substitutions, and
`Stacks.Sites.Conormal.sub_mem_sq_of_substitution` — the homotopy of Stacks 00S1 (2) in degree
`-1` — identifies the restriction of `q` with the image of the truncated witness modulo
`(Ker φ₁')²`.  No second-order Taylor expansion appears.

Two spellings of a variable substitution are in play: the truncation lemmas state their
conclusions with `MvPolynomial.rename`, whose `RingHom` coercion is only definitionally the one
carried by the objects of `CommRingCat`, while every map built here is written with
`MvPolynomial.eval₂Hom` so that `MvPolynomial.eval₂Hom_C` and `MvPolynomial.eval₂Hom_X'`
apply.  The two presentations on truncated variable sets are composites in `CommRingCat`, which
keeps `rename` confined to the places where the quoted lemmas already put it.

The algebra structure on a polynomial ring induced by `MvPolynomial.C` is not definitionally
the standard one, which is why the derivative criterion is quoted as
`KaehlerDifferential.one_tmul_D_eq_zero_iff_pderiv_mem`, taking the structural map as a
hypothesis.

## References

* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of
  the naive cotangent complex from the presentation, of which this is the injectivity half in
  degree `-1` at the ring level.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the homotopy
  behind the comparison of two factorisations.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
-/

@[expose] public section

open CategoryTheory TensorProduct

universe w

namespace Stacks.Sites.Conormal

section Ideals

variable {A : Type*} [CommRing A]

/-- The square of an ideal is monotone in the ideal. -/
private theorem mem_sq_of_le_of_mem_sq {I J : Ideal A} (hIJ : I ≤ J) {z : A} (hz : z ∈ I ^ 2) :
    z ∈ J ^ 2 := by
  rw [pow_two] at hz ⊢
  exact Submodule.mul_induction_on hz (fun m hm n hn ↦ Ideal.mul_mem_mul (hIJ hm) (hIJ hn))
    fun x y hx hy ↦ Ideal.add_mem _ hx hy

end Ideals

section Abstract

variable {Pr Ps P' T R₀ : CommRingCat.{w}}

/-- **The step the homotopy supplies.**  Let `φ` factor through `φ₁` by `σ` and through `φ'` by
`t`, let `φ₁` factor through `φ'` by `ρ`, all over a base `R₀`, and let `q` lie in the kernel of
`φ` with vanishing universal differential.  If moreover `σ q` is a prescribed element `ps` of
the square of the kernel of `φ₁`, then `t q` lies in the square of the kernel of `φ'`: it
differs from `ρ ps` by the homotopy of Stacks 00S1 (2) in degree `-1`. -/
private theorem mem_ker_sq_of_substitution_eq (φ : Pr ⟶ T) (φ₁ : Ps ⟶ T) (φ' : P' ⟶ T)
    (σ : Pr ⟶ Ps) (ρ : Ps ⟶ P') (t : Pr ⟶ P')
    (hρ : ρ ≫ φ' = φ₁) (hσ : σ ≫ φ₁ = φ) (ht : t ≫ φ' = φ)
    (b : R₀ ⟶ Pr) (b₁ : R₀ ⟶ Ps) (b₂ : R₀ ⟶ P')
    (hbσ : b ≫ σ = b₁) (hbρ : b₁ ≫ ρ = b₂) (hbt : b ≫ t = b₂)
    (q : Pr) (hq : q ∈ RingHom.ker φ.hom)
    (hd : (1 : Pr ⧸ RingHom.ker φ.hom) ⊗ₜ[Pr]
      CommRingCat.KaehlerDifferential.d (f := b) q = 0)
    (ps : Ps) (hps : σ.hom q = ps) (hpsq : ps ∈ RingHom.ker φ₁.hom ^ 2) :
    t.hom q ∈ RingHom.ker φ'.hom ^ 2 := by
  have hsub := sub_mem_sq_of_substitution φ φ₁ φ' ρ σ t hρ hσ ht b b₁ b₂ hbσ hbρ hbt q hq hd
  have hρps : ρ.hom (σ.hom q) ∈ RingHom.ker φ'.hom ^ 2 := by
    rw [hps]
    exact map_mem_ker_sq_of_fac φ₁ φ' ρ hρ hpsq
  rw [show t.hom q = ρ.hom (σ.hom q) - (ρ.hom (σ.hom q) - t.hom q) from
    (sub_sub_cancel _ _).symm]
  exact Ideal.sub_mem _ hρps hsub

end Abstract

section Lifts

variable {R₀ R₀' T₀ T : CommRingCat.{w}} {ι₁ ι₂ ι₁' : Type w}

/-- **The two truncated substitutions commute with the inclusions of the truncated variable
sets.**  Renaming the variables of a finite set `v ⊆ ι₁` to a finite set `s ⊆ ι₂` by `h₁` and
then including `s` into `ι₂` is the same as including `v` into `ι₁` and then substituting the
variables along `h₁`. -/
private theorem rename_eval₂Hom_eq (h₁ : ι₁ → ι₂) {v : Finset ι₁} {s : Finset ι₂}
    (hs : ∀ i : {x // x ∈ v}, h₁ i.1 ∈ s) (p : MvPolynomial {x // x ∈ v} R₀) :
    MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι₂)
        (MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i : {x // x ∈ v} ↦ MvPolynomial.X (⟨h₁ i.1, hs i⟩ : {x // x ∈ s})) p) =
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i))
        (MvPolynomial.rename (Subtype.val : {x // x ∈ v} → ι₁) p) := by
  have h : (MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι₂)).toRingHom.comp
        (MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i : {x // x ∈ v} ↦ MvPolynomial.X (⟨h₁ i.1, hs i⟩ : {x // x ∈ s}))) =
      (MvPolynomial.eval₂Hom (R := R₀) MvPolynomial.C
          (fun i ↦ MvPolynomial.X (h₁ i))).comp
        (MvPolynomial.rename (Subtype.val : {x // x ∈ v} → ι₁)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp
    · simp
  exact RingHom.congr_fun h p

/-- **The base map of a polynomial presentation is absorbed by a substitution.**  Composing the
coefficient inclusion with the substitution `eval₂Hom g h` recovers `g`. -/
private theorem ofHom_C_comp_eval₂Hom {R : CommRingCat.{w}} {S : Type w} [CommRing S]
    {κ : Type w} (g : R →+* S) (h : κ → S) :
    (CommRingCat.ofHom (MvPolynomial.C (σ := κ) (R := R)) :
          R ⟶ CommRingCat.of (MvPolynomial κ R)) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom g h) =
      CommRingCat.ofHom g :=
  CommRingCat.hom_ext (RingHom.ext fun r ↦ MvPolynomial.eval₂Hom_C g h r)

/-- **The derivative criterion at a truncated presentation.**  If every partial derivative of a
polynomial on a finite set of variables lies in the kernel of a presentation of that polynomial
ring, then the universal differential of that polynomial vanishes in the conormal term of the
presentation, the base being the coefficient inclusion. -/
private theorem one_tmul_d_eq_zero_of_pderiv_mem {ι : Type w} {v : Finset ι}
    (ψ : CommRingCat.of (MvPolynomial {x // x ∈ v} R₀) ⟶ T)
    (p : MvPolynomial {x // x ∈ v} R₀)
    (hpd : ∀ j, MvPolynomial.pderiv j p ∈ RingHom.ker ψ.hom) :
    TensorProduct.tmul (CommRingCat.of (MvPolynomial {x // x ∈ v} R₀))
        (1 : CommRingCat.of (MvPolynomial {x // x ∈ v} R₀) ⧸ RingHom.ker ψ.hom)
        (CommRingCat.KaehlerDifferential.d
          (f := (CommRingCat.ofHom (MvPolynomial.C (σ := {x // x ∈ v}) (R := R₀)) :
            R₀ ⟶ CommRingCat.of (MvPolynomial {x // x ∈ v} R₀))) p) = 0 :=
  (KaehlerDifferential.one_tmul_D_eq_zero_iff_pderiv_mem
    (inst := (CommRingCat.ofHom (MvPolynomial.C (σ := {x // x ∈ v}) (R := R₀))).hom.toAlgebra)
    (fun _ ↦ rfl) (RingHom.ker ψ.hom) p).mpr hpd

variable (rr : R₀ ⟶ R₀') (τ : T₀ ⟶ T) (h₁ : ι₁ → ι₂) (e₁ : ι₁ → ι₁')
  (φ₁ : CommRingCat.of (MvPolynomial ι₁ R₀) ⟶ T₀)
  (φ₂ : CommRingCat.of (MvPolynomial ι₂ R₀) ⟶ T₀)
  (φ₁' : CommRingCat.of (MvPolynomial ι₁' R₀') ⟶ T)

/-- **The two truncated presentations are compatible with the truncated substitution.**  The
substitution of the variables of `v` into those of `s` along `h₁` factors the presentation
`R₀[v] ⟶ T` through the presentation `R₀[s] ⟶ T`, both read over the covering object by `τ`. -/
private theorem fac_truncSubst
    (hu : ∀ p : MvPolynomial ι₁ R₀,
      φ₂.hom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) p) = φ₁.hom p)
    {v : Finset ι₁} {s : Finset ι₂} (hs : ∀ i : {x // x ∈ v}, h₁ i.1 ∈ s) :
    CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i : {x // x ∈ v} ↦ MvPolynomial.X (⟨h₁ i.1, hs i⟩ : {x // x ∈ s}))) ≫
        (CommRingCat.ofHom (MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι₂)).toRingHom ≫
          φ₂ ≫ τ) =
      CommRingCat.ofHom (MvPolynomial.rename (Subtype.val : {x // x ∈ v} → ι₁)).toRingHom ≫
        φ₁ ≫ τ := by
  refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_)
  · have h := hu (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h
    simpa using congrArg τ.hom h
  · have h := hu (MvPolynomial.X i.1)
    rw [MvPolynomial.eval₂Hom_X'] at h
    simpa using congrArg τ.hom h

/-- **The lifts factor the truncated second presentation through the restricted first one.**
Substituting, for each variable in `s`, a lift through `φ₁'` of its image in `T` factors the
presentation `R₀[s] ⟶ T` through `φ₁'`. -/
private theorem fac_lift
    (hu : ∀ p : MvPolynomial ι₁ R₀,
      φ₂.hom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) p) = φ₁.hom p)
    (hres : ∀ p : MvPolynomial ι₁ R₀,
      φ₁'.hom (MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
        (fun i ↦ MvPolynomial.X (e₁ i)) p) = τ.hom (φ₁.hom p))
    {s : Finset ι₂} (c : ι₂ → MvPolynomial ι₁' R₀')
    (hc : ∀ j ∈ s, φ₁'.hom (c j) = τ.hom (φ₂.hom (MvPolynomial.X j))) :
    CommRingCat.ofHom (MvPolynomial.eval₂Hom
          ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
          (fun j : {x // x ∈ s} ↦ c j.1)) ≫ φ₁' =
      CommRingCat.ofHom (MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι₂)).toRingHom ≫
        φ₂ ≫ τ := by
  refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun j ↦ ?_)
  · have h₁' := hres (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h₁'
    have h₂' := hu (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h₂'
    simpa using h₁'.trans (congrArg τ.hom h₂').symm
  · simpa using hc j.1 j.2

/-- **The restriction factors the truncated first presentation through the restricted one.**
Relabelling the variables of `v` by `e₁` and restricting the coefficients by `rr` factors the
presentation `R₀[v] ⟶ T` through `φ₁'`. -/
private theorem fac_restriction
    (hres : ∀ p : MvPolynomial ι₁ R₀,
      φ₁'.hom (MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
        (fun i ↦ MvPolynomial.X (e₁ i)) p) = τ.hom (φ₁.hom p))
    {v : Finset ι₁} :
    CommRingCat.ofHom (MvPolynomial.eval₂Hom
          ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
          (fun i : {x // x ∈ v} ↦ MvPolynomial.X (e₁ i.1))) ≫ φ₁' =
      CommRingCat.ofHom (MvPolynomial.rename (Subtype.val : {x // x ∈ v} → ι₁)).toRingHom ≫
        φ₁ ≫ τ := by
  refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_)
  · have h := hres (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h
    simpa using h
  · have h := hres (MvPolynomial.X i.1)
    rw [MvPolynomial.eval₂Hom_X'] at h
    simpa using h

/-- Pulling an element of the kernel of `φ` back along `f`, then pushing forward along `τ`,
stays in the kernel. -/
private theorem mem_ker_comp_of_map_mem_ker {A B T₀ T : CommRingCat.{w}} (f : A ⟶ B)
    (φ : B ⟶ T₀) (τ : T₀ ⟶ T) {x : A} (hx : f.hom x ∈ RingHom.ker φ.hom) :
    x ∈ RingHom.ker (f ≫ φ ≫ τ).hom := by
  change τ.hom (φ.hom (f.hom x)) = 0
  rw [RingHom.mem_ker.mp hx, map_zero]

/-- **The descent, once the lifts are given.**  Let `q` lie, with all of its partial
derivatives, in the kernel of `φ₁`; let `ps`, a polynomial on a finite set `s` of variables of
the second presentation containing the image of the variables of `q`, witness that `u q` lies
in the square of the kernel of `φ₂`; and let every variable in `s` have its image in `T` lifted
through `φ₁'`.  Then the restriction of `q` lies in the square of the kernel of `φ₁'`.

Both `q` and the witness have already been truncated, the first to its own variables and the
second to `s`; the three presentations on those variable sets and on `ι₁'` form the triangle
the homotopy of Stacks 00S1 (2) applies to. -/
private theorem mem_ker_sq_of_lifts
    (hu : ∀ p : MvPolynomial ι₁ R₀,
      φ₂.hom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) p) = φ₁.hom p)
    (hres : ∀ p : MvPolynomial ι₁ R₀,
      φ₁'.hom (MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
        (fun i ↦ MvPolynomial.X (e₁ i)) p) = τ.hom (φ₁.hom p))
    {q : MvPolynomial ι₁ R₀} (hq : q ∈ RingHom.ker φ₁.hom)
    {s : Finset ι₂} (hs : ∀ i : {x // x ∈ q.vars}, h₁ i.1 ∈ s)
    (c : ι₂ → MvPolynomial ι₁' R₀')
    (hc : ∀ j ∈ s, φ₁'.hom (c j) = τ.hom (φ₂.hom (MvPolynomial.X j)))
    {p₀ : MvPolynomial {x // x ∈ q.vars} R₀}
    (hp₀ : MvPolynomial.rename (Subtype.val : {x // x ∈ q.vars} → ι₁) p₀ = q)
    (hpd₀ : ∀ j : {x // x ∈ q.vars},
      MvPolynomial.rename (Subtype.val : {x // x ∈ q.vars} → ι₁)
        (MvPolynomial.pderiv j p₀) ∈ RingHom.ker φ₁.hom)
    {ps : MvPolynomial {x // x ∈ s} R₀}
    (hps : MvPolynomial.rename (Subtype.val : {x // x ∈ s} → ι₂) ps =
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) q)
    (hpsq : ps ∈ RingHom.ker (φ₂.hom.comp (MvPolynomial.rename
      (Subtype.val : {x // x ∈ s} → ι₂)).toRingHom) ^ 2) :
    MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
        (fun i ↦ MvPolynomial.X (e₁ i)) q ∈ RingHom.ker φ₁'.hom ^ 2 := by
  have hq₀ : p₀ ∈ RingHom.ker (CommRingCat.ofHom (MvPolynomial.rename
      (Subtype.val : {x // x ∈ q.vars} → ι₁)).toRingHom ≫ φ₁ ≫ τ).hom :=
    mem_ker_comp_of_map_mem_ker _ _ _ (by simpa [hp₀] using hq)
  have hpdker : ∀ j, MvPolynomial.pderiv j p₀ ∈ RingHom.ker (CommRingCat.ofHom
      (MvPolynomial.rename (Subtype.val : {x // x ∈ q.vars} → ι₁)).toRingHom ≫ φ₁ ≫ τ).hom :=
    fun j ↦ mem_ker_comp_of_map_mem_ker _ _ _ (hpd₀ j)
  have hpsq' : ps ∈ RingHom.ker (CommRingCat.ofHom (MvPolynomial.rename
      (Subtype.val : {x // x ∈ s} → ι₂)).toRingHom ≫ φ₂ ≫ τ).hom ^ 2 :=
    mem_sq_of_le_of_mem_sq (fun _ hx ↦ mem_ker_comp_of_map_mem_ker _ _ _ hx) hpsq
  have hσps : (CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : {x // x ∈ q.vars} ↦
        MvPolynomial.X (⟨h₁ i.1, hs i⟩ : {x // x ∈ s})))).hom p₀ = ps := by
    have h := rename_eval₂Hom_eq (R₀ := R₀) h₁ hs p₀
    rw [hp₀] at h
    exact MvPolynomial.rename_injective _ Subtype.val_injective (h.trans hps.symm)
  have hteq : MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
        (fun i : {x // x ∈ q.vars} ↦ MvPolynomial.X (e₁ i.1)) p₀ =
      MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
        (fun i ↦ MvPolynomial.X (e₁ i)) q := by
    refine Eq.trans ?_ (congrArg (fun z ↦ MvPolynomial.eval₂Hom
      ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
      (fun i ↦ MvPolynomial.X (e₁ i)) z) hp₀)
    exact (MvPolynomial.eval₂Hom_rename
      ((MvPolynomial.C (σ := ι₁') (R := R₀')).comp rr.hom)
      (Subtype.val : {x // x ∈ q.vars} → ι₁)
      (fun i ↦ MvPolynomial.X (e₁ i)) p₀).symm
  rw [← hteq]
  exact mem_ker_sq_of_substitution_eq _ _ _ _ _ _
    (fac_lift rr τ h₁ e₁ φ₁ φ₂ φ₁' hu hres c hc)
    (fac_truncSubst τ h₁ φ₁ φ₂ hu hs)
    (fac_restriction rr τ e₁ φ₁ φ₁' hres (v := q.vars))
    _ _ _ (ofHom_C_comp_eval₂Hom _ _) (ofHom_C_comp_eval₂Hom _ _) (ofHom_C_comp_eval₂Hom _ _)
    p₀ hq₀ (one_tmul_d_eq_zero_of_pderiv_mem _ p₀ hpdker) ps hσps hpsq'

end Lifts

section Descent

/-- **The injectivity half of Stacks 08TY in degree `-1`, at the ring level.**  Let `φ₁` and
`φ₂` be two polynomial presentations of one ring over a base `R₀`, with `h₁ : ι₁ → ι₂` a map of
the two families of variables whose substitution `u` factors `φ₁` through `φ₂`, and let `φ₁'`
be `φ₁` read over a covering object: coefficients restricted by `rr`, variables relabelled by
`e₁` and target changed by `τ`.  Let `q` lie in the kernel of `φ₁` together with all of its
partial derivatives, that is let its conormal class be killed by the conormal map, and let its
image `u q` lie in the *square* of the kernel of `φ₂`.

Then there is a finite set `s` of variables of the second presentation such that, as soon as
the image in `T` of every `φ₂ (X j)` with `j ∈ s` lifts through `φ₁'`, the restriction of `q`
lies in the square of the kernel of `φ₁'`.

The finite set is produced *before* the lifts are consumed, because on a site a lift of a
generator through a locally surjective presentation exists only after passing to a covering,
and which covering is needed depends on which finitely many generators have to be lifted. -/
theorem exists_finset_restriction_mem_ker_sq
    {R₀ R₀' T₀ T : CommRingCat.{w}} {ι₁ ι₂ ι₁' : Type w}
    (rr : R₀ ⟶ R₀') (τ : T₀ ⟶ T) (h₁ : ι₁ → ι₂) (e₁ : ι₁ → ι₁')
    (φ₁ : CommRingCat.of (MvPolynomial ι₁ R₀) ⟶ T₀)
    (φ₂ : CommRingCat.of (MvPolynomial ι₂ R₀) ⟶ T₀)
    (φ₁' : CommRingCat.of (MvPolynomial ι₁' R₀') ⟶ T)
    (hu : ∀ p : MvPolynomial ι₁ R₀,
      φ₂.hom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) p) = φ₁.hom p)
    (hres : ∀ p : MvPolynomial ι₁ R₀,
      φ₁'.hom (MvPolynomial.eval₂Hom (MvPolynomial.C.comp rr.hom)
        (fun i ↦ MvPolynomial.X (e₁ i)) p) = τ.hom (φ₁.hom p))
    (q : MvPolynomial ι₁ R₀) (hq : q ∈ RingHom.ker φ₁.hom)
    (hpd : ∀ i, MvPolynomial.pderiv i q ∈ RingHom.ker φ₁.hom)
    (hsq : MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) q ∈
      RingHom.ker φ₂.hom ^ 2) :
    ∃ s : Finset ι₂, ∀ c : ι₂ → MvPolynomial ι₁' R₀',
      (∀ j ∈ s, φ₁'.hom (c j) = τ.hom (φ₂.hom (MvPolynomial.X j))) →
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp rr.hom) (fun i ↦ MvPolynomial.X (e₁ i)) q ∈
        RingHom.ker φ₁'.hom ^ 2 := by
  classical
  obtain ⟨s, hs₀, ps, hps, hpsq⟩ :=
    exists_finset_rename_mem_ker_sq φ₂.hom (q.vars.image h₁)
      (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ MvPolynomial.X (h₁ i)) q) hsq
  refine ⟨s, fun c hc ↦ ?_⟩
  obtain ⟨p₀, hp₀, hpd₀⟩ :=
    exists_finset_rename_forall_rename_pderiv_mem (RingHom.ker φ₁.hom) q hpd
  exact mem_ker_sq_of_lifts rr τ h₁ e₁ φ₁ φ₂ φ₁' hu hres hq
    (fun i ↦ hs₀ (Finset.mem_image_of_mem h₁ i.2)) c hc hp₀ hpd₀ hps hpsq

end Descent

end Stacks.Sites.Conormal

end
