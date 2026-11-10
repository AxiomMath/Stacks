module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDescentDatum
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineEssentialSurjectivity

/-!
# Cancelling a base change against a self-product of rings

A descent datum built from the sections of a presheaf of modules over a covering object needs two
comparisons: an additive identification `B ⊗[A] N ≃+ Nv` of a base change of the sections over the
covering object with the sections over the double self-product, and a map
`B ⊗[A] (B ⊗[A] N) →+ N₃` into the sections over the triple self-product.  What quasi-coherence
supplies instead is a comparison in the *coefficient ring of the overlap*: the sections over the
double self-product are the base change of the sections over the covering object along the ring
map of one projection.  Passing from one to the other is a cancellation
`D ⊗[C] N ≃ B ⊗[A] N` for a ring `D` which is a tensor product `B ⊗[A] C`, read through a ring
isomorphism exhibiting that tensor product.

This cancellation is in Mathlib as `Algebra.IsPushout.cancelBaseChange`, but in a form which does
not apply here.  That statement takes the two ring maps `C → D` and `B → D` from the two `Algebra`
instances it quantifies over, and for a *self*-product — the case `C = B`, which is the one the
double overlap of a single covering morphism presents — those two instances are the same instance,
so the hypothesis `Algebra.IsPushout A B B D` cannot name the two inclusions of `B` into `B ⊗[A] B`
separately and the conclusion is not the cancellation wanted.  The statements below therefore take
one of the two maps as an explicit `RingHom` argument and the identification of `D` with the
tensor product as an explicit `RingEquiv`, which keeps the diagonal case admissible; this is the
same reason a triple base change has to take its three algebra structures as arguments.

Nothing is assumed flat, and no finiteness or affineness enters: the content is that a tensor
product over `A` of a free rank-one situation cancels, and the proof is an explicit pair of
additive maps checked on pure tensors.  The maps are built with `TensorProduct.liftAddHom`, so no
module structure over `A` on the target is needed to construct them; the `A`-linearity of the
resulting equivalence is proved afterwards, and is what makes the comparison one degree up
available, since tensoring the first comparison with `B` needs it to be linear.

## Main results

* `Module.Descent.exists_cancelBaseChange`: **a base change along `A → B` of a module over `C` is
  the base change along `C → D` of that module**, when `D` is `B ⊗[A] C` and the module over `C`
  base-changes to the given module over `D`.  The equivalence carries `b ⊗ₜ n` to `v₁ b • ρ n`,
  where `v₁ : B →+* D` is the explicit map corresponding to `b ↦ b ⊗ₜ 1`.
* `Module.Descent.exists_cancelBaseChange_pair`: **the two comparisons of a descent datum at
  once**, the second characterised in terms of the first.  This is the shape
  `PresheafOfModules.exists_datum_of_baseChange` consumes: its hypothesis on the comparison one
  degree up mentions the comparison one degree down, so the two cannot be obtained from separate
  existential statements.
* `Module.Descent.exists_cancelBaseChange_pi`: **the same cancellation for a finite family**, where
  the base change is along the product of the coefficient rings of the members and the target is
  the double product of the sections over the overlaps.  This is the instantiation a covering
  family needs, the product being the ring over which faithful flatness is available.
* `Module.Descent.span_pi_apply_eq_top`: **a span over a product of rings restricts to a span over
  each factor**, which is how a span condition proved over the product of the coefficient rings of
  a covering family is read off at a single member.
* `SheafOfModules.sectionSpan_eq_top_of_span_eq_top`: **a span over any ring acting through the
  sections of the structure sheaf is a span over those sections**, which turns the previous one
  into `SheafOfModules.sectionSpan _ = ⊤`.
* `SheafOfModules.sectionSpan_eq_top_of_family_datum`: **the sections over each member of a
  covering family are spanned by the restrictions of the sections over the object covered**, from a
  descent datum on the product of the modules of sections, the amalgamation half of the sheaf axiom
  for the family, and flatness of the product of the coefficient rings.

The last two results are the step after the descent datum rather than before it.  A span condition
obtained from `Module.Descent.span_range_eq_top_of_comparison` for a covering family is a span over
the product `∀ i, B i`, inside the product `∀ i, N(Y i)` of the modules of sections; what
`AlgebraicGeometry.FibredSite.isGeneratedByUnit_over_of_sectionSpan_eq_top` asks for is a span over
the sections of the structure sheaf at a single member.  Those two steps are independent of
everything above and of each other.

## Implementation notes

The hypotheses on the ring isomorphism are its values on the two pure tensors `b ⊗ₜ 1` and
`1 ⊗ₜ c` rather than a statement about the induced algebra structures, since a consumer holding
`AlgebraicGeometry.FibredSite.algEquivTensorGammaOfIsPullback` holds exactly those values, by
`AlgebraicGeometry.FibredSite.algEquivTensorGammaOfIsPullback_tmul`.  Only the second one is
stated through `algebraMap`, because that is the map along which the base change of the module is
taken, and a base change has to be taken along an `Algebra` instance.

The comparison one degree up is a composite of the first comparison tensored with `B` and a second
cancellation, so its injectivity is that of a composite of two injective maps rather than a
separate argument.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

namespace Module.Descent

/-- **Cancelling a base change against a self-product of rings.**  Let `A` be a base ring, `B` and
`C` two `A`-algebras, and `D` a `C`-algebra identified with `B ⊗[A] C` by a ring isomorphism `ψ`
carrying `b ⊗ₜ 1` to a given ring map `v₁ b` and `1 ⊗ₜ c` to the structural map of `D` over `C`.
Let `N` be a `C`-module and `Nv` a `D`-module which is the base change of `N` along `C → D`, the
comparison being `ρ`.  Then `Nv` is also, additively and `A`-linearly, the base change of `N`
along `A → B`, by an equivalence carrying `b ⊗ₜ n` to `v₁ b • ρ n`.

The two maps `B → D` and `C → D` are not interchangeable here even when `B = C`, and the point of
taking `v₁` as an explicit argument rather than as `algebraMap B D` is exactly that case: a double
self-product of a covering morphism has `B = C`, its two projections induce the two inclusions of
`B` into `B ⊗[A] B`, and an instance-valued statement such as `Algebra.IsPushout.cancelBaseChange`
collapses them. -/
theorem exists_cancelBaseChange
    (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra C D]
    {N : Type*} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower A C N]
    {Nv : Type*} [AddCommGroup Nv] [Module A Nv] [Module C Nv] [Module D Nv]
    [IsScalarTower A C Nv] [IsScalarTower C D Nv]
    (v₁ : B →+* D) (ψ : B ⊗[A] C ≃+* D)
    (hv₁ : ∀ b : B, ψ (b ⊗ₜ[A] (1 : C)) = v₁ b)
    (hv₂ : ∀ c : C, ψ ((1 : B) ⊗ₜ[A] c) = algebraMap C D c)
    (ρ : N →ₗ[C] Nv) (hρ : Function.Bijective (ρ.liftBaseChange D)) :
    ∃ e : B ⊗[A] N ≃ₗ[A] Nv, ∀ (b : B) (n : N), e (b ⊗ₜ[A] n) = v₁ b • ρ n := by
  have hbase : ∀ a : A, v₁ (algebraMap A B a) = algebraMap C D (algebraMap A C a) := by
    intro a
    rw [← hv₁, ← hv₂, Algebra.algebraMap_eq_smul_one (R := A) (A := B) a,
      Algebra.algebraMap_eq_smul_one (R := A) (A := C) a, TensorProduct.smul_tmul]
  let g : B ⊗[A] C →+ N →+ B ⊗[A] N :=
    TensorProduct.liftAddHom
      { toFun := fun b =>
          { toFun := fun c =>
              { toFun := fun n => b ⊗ₜ[A] (c • n)
                map_zero' := by simp
                map_add' := fun n n' => by rw [smul_add, TensorProduct.tmul_add] }
            map_zero' := by ext n; simp
            map_add' := fun c c' => by ext n; simp [add_smul, TensorProduct.tmul_add] }
        map_zero' := by ext c n; simp
        map_add' := fun b b' => by ext c n; simp [TensorProduct.add_tmul] }
      fun a b c => by
        ext n
        change (a • b) ⊗ₜ[A] (c • n) = b ⊗ₜ[A] ((a • c) • n)
        rw [TensorProduct.smul_tmul, smul_assoc]
  have hg : ∀ (b : B) (c : C) (n : N), g (b ⊗ₜ[A] c) n = b ⊗ₜ[A] (c • n) := fun _ _ _ => rfl
  let α : B ⊗[A] N →+ D ⊗[C] N :=
    TensorProduct.liftAddHom
      { toFun := fun b =>
          { toFun := fun n => (v₁ b) ⊗ₜ[C] n
            map_zero' := by simp
            map_add' := fun n n' => TensorProduct.tmul_add _ _ _ }
        map_zero' := by ext n; simp
        map_add' := fun b b' => by ext n; simp [TensorProduct.add_tmul] }
      fun a b n => by
        change v₁ (a • b) ⊗ₜ[C] n = v₁ b ⊗ₜ[C] (a • n)
        rw [← IsScalarTower.algebraMap_smul C a n, ← TensorProduct.smul_tmul,
          Algebra.smul_def a b, map_mul, hbase, Algebra.smul_def (algebraMap A C a) (v₁ b)]
  have hα : ∀ (b : B) (n : N), α (b ⊗ₜ[A] n) = v₁ b ⊗ₜ[C] n := fun _ _ => rfl
  have hψ₁ : ∀ b : B, ψ.symm (v₁ b) = b ⊗ₜ[A] (1 : C) := fun b => ψ.symm_apply_eq.2 (hv₁ b).symm
  have hψ₂ : ∀ c : C, ψ.symm (algebraMap C D c) = (1 : B) ⊗ₜ[A] c :=
    fun c => ψ.symm_apply_eq.2 (hv₂ c).symm
  have hgmul : ∀ (c : C) (y : B ⊗[A] C) (n : N),
      g (((1 : B) ⊗ₜ[A] c) * y) n = g y (c • n) := by
    intro c y n
    induction y with
    | tmul b c' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hg, hg, smul_smul, mul_comm c c']
    | add y y' hy hy' => simp [mul_add, hy, hy']
  let β : D ⊗[C] N →+ B ⊗[A] N :=
    TensorProduct.liftAddHom (g.comp (ψ.symm.toAddEquiv : D ≃+ B ⊗[A] C).toAddMonoidHom)
      fun c d n => by
        change g (ψ.symm (c • d)) n = g (ψ.symm d) (c • n)
        rw [Algebra.smul_def, map_mul, hψ₂, hgmul]
  have hβ : ∀ (d : D) (n : N), β (d ⊗ₜ[C] n) = g (ψ.symm d) n := fun _ _ => rfl
  have hαg : ∀ (y : B ⊗[A] C) (n : N), α (g y n) = ψ y ⊗ₜ[C] n := by
    intro y n
    induction y with
    | tmul b c =>
      rw [hg, hα, ← TensorProduct.smul_tmul, Algebra.smul_def, ← hv₂, ← hv₁, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add y y' hy hy' => simp [hy, hy', TensorProduct.add_tmul]
  have hleft : ∀ x : B ⊗[A] N, β (α x) = x := by
    intro x
    induction x with
    | tmul b n => rw [hα, hβ, hψ₁, hg, one_smul]
    | add x x' hx hx' => simp [hx, hx']
  have hright : ∀ z : D ⊗[C] N, α (β z) = z := by
    intro z
    induction z with
    | tmul d n => rw [hβ, hαg, ψ.apply_symm_apply]
    | add z z' hz hz' => simp [hz, hz']
  have hαbij : Function.Bijective α :=
    Function.bijective_iff_has_inverse.2 ⟨β, hleft, hright⟩
  let e₀ : B ⊗[A] N ≃+ Nv :=
    (AddEquiv.ofBijective α hαbij).trans
      (AddEquiv.ofBijective (ρ.liftBaseChange D).toAddMonoidHom hρ)
  have he₀ : ∀ (b : B) (n : N), e₀ (b ⊗ₜ[A] n) = v₁ b • ρ n := fun b n => by
    change (ρ.liftBaseChange D) (α (b ⊗ₜ[A] n)) = v₁ b • ρ n
    rw [hα]
    rfl
  refine ⟨AddEquiv.toLinearEquiv e₀ ?_, he₀⟩
  intro a x
  induction x with
  | tmul b n =>
    rw [TensorProduct.smul_tmul', he₀, he₀, Algebra.smul_def a b, map_mul, hbase,
      ← IsScalarTower.algebraMap_smul C a (v₁ b • ρ n),
      ← IsScalarTower.algebraMap_smul D (algebraMap A C a) (v₁ b • ρ n), smul_smul]
  | add x x' hx hx' => simp [hx, hx']

/-- **The two comparisons of a descent datum at once, the second characterised through the
first.**  Let `D` be identified with `B ⊗[A] B` and `E` with `B ⊗[A] D`, by ring isomorphisms whose
values on pure tensors are given by the explicit maps `v₁ : B →+* D` and `u₁ : B →+* E` and by the
structural maps.  Let the `D`-module `Nv` be the base change of the `B`-module `N` and the
`E`-module `N₃` the base change of `Nv`.  Then there are an additive identification
`B ⊗[A] N ≃+ Nv` and an injection `B ⊗[A] (B ⊗[A] N) →+ N₃` whose values on pure tensors are
`v₁ b • ρ n` and `u₁ b • ρ₃ (e y)`.

This is the shape `PresheafOfModules.exists_datum_of_baseChange` takes its two comparisons in:
the hypothesis characterising the second one refers to the first, so the two must be produced by a
single statement — an existential giving them separately would allow no later hypothesis about the
same pair.

The second comparison is the first tensored with `B` followed by a second cancellation, so it is
injective rather than bijective only because its source is written as an iterated tensor product;
its image is all of `N₃`. -/
theorem exists_cancelBaseChange_pair
    (A B D E : Type*) [CommRing A] [CommRing B] [CommRing D] [CommRing E]
    [Algebra A B] [Algebra A D] [Algebra B D] [Algebra D E]
    {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    {Nv : Type*} [AddCommGroup Nv] [Module A Nv] [Module B Nv] [Module D Nv]
    [IsScalarTower A B Nv] [IsScalarTower B D Nv] [IsScalarTower A D Nv]
    {N₃ : Type*} [AddCommGroup N₃] [Module A N₃] [Module D N₃] [Module E N₃]
    [IsScalarTower A D N₃] [IsScalarTower D E N₃]
    (v₁ : B →+* D) (ψ : B ⊗[A] B ≃+* D)
    (hv₁ : ∀ b : B, ψ (b ⊗ₜ[A] (1 : B)) = v₁ b)
    (hv₂ : ∀ b : B, ψ ((1 : B) ⊗ₜ[A] b) = algebraMap B D b)
    (u₁ : B →+* E) (ψ₃ : B ⊗[A] D ≃+* E)
    (hu₁ : ∀ b : B, ψ₃ (b ⊗ₜ[A] (1 : D)) = u₁ b)
    (hu₂ : ∀ d : D, ψ₃ ((1 : B) ⊗ₜ[A] d) = algebraMap D E d)
    (ρ : N →ₗ[B] Nv) (hρ : Function.Bijective (ρ.liftBaseChange D))
    (ρ₃ : Nv →ₗ[D] N₃) (hρ₃ : Function.Bijective (ρ₃.liftBaseChange E)) :
    ∃ (e : B ⊗[A] N ≃+ Nv) (e₃ : B ⊗[A] (B ⊗[A] N) →+ N₃),
      (∀ (b : B) (n : N), e (b ⊗ₜ[A] n) = v₁ b • ρ n) ∧ Function.Injective e₃ ∧
        ∀ (b : B) (y : B ⊗[A] N), e₃ (b ⊗ₜ[A] y) = u₁ b • ρ₃ (e y) := by
  obtain ⟨e, he⟩ := exists_cancelBaseChange A B B D v₁ ψ hv₁ hv₂ ρ hρ
  obtain ⟨f, hf⟩ := exists_cancelBaseChange A B D E u₁ ψ₃ hu₁ hu₂ ρ₃ hρ₃
  let g := (TensorProduct.congr (LinearEquiv.refl A B) e).trans f
  refine ⟨e.toAddEquiv, g.toAddMonoidHom, he, g.injective, fun b y => ?_⟩
  change f (TensorProduct.congr (LinearEquiv.refl A B) e (b ⊗ₜ[A] y)) = u₁ b • ρ₃ (e y)
  rw [TensorProduct.congr_tmul, hf]
  rfl

/-- **The cancellation for a finite family.**  A covering family `{Y i ⟶ T}` presents the sections
over its overlaps as base changes member by member, and the descent datum it carries lives over the
product `∀ i, B i` of the coefficient rings.  This statement assembles the member-wise
cancellations into one: if for each pair `(i, k)` the ring `D i k` is `B i ⊗[A] C k` and the
`D i k`-module `Mv i k` is the base change of the `C k`-module `M k`, then the base change along
`A → ∀ i, B i` of the product `∀ k, M k` is the double product `∀ i k, Mv i k`, by an equivalence
carrying `s ⊗ₜ u` at the slot `(i, k)` to `v i k (s i) • ρ i k (u k)`.

Both index types are finite because the identification is the one of
`TensorProduct.piRight`: a tensor product commutes with a product of modules only over a finite
index.  Only one family of `Algebra` instances is assumed, `Algebra (C k) (D i k)`; the other
inclusion of a coefficient ring into the ring of an overlap is the explicit `v i k`, which is what
makes the diagonal `i = k` of a self-product admissible.

The equivalence is `A`-linear and not merely additive so that it can be tensored with
`∀ i, B i` again, which is how the comparison one degree up is obtained from it — the step
`Module.Descent.exists_cancelBaseChange_pair` performs in the one-member case. -/
theorem exists_cancelBaseChange_pi
    (A : Type*) [CommRing A] {ι κ : Type*} [Finite ι] [Finite κ]
    (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (C : κ → Type*) [∀ k, CommRing (C k)] [∀ k, Algebra A (C k)]
    (D : ι → κ → Type*) [∀ i k, CommRing (D i k)] [∀ i k, Algebra (C k) (D i k)]
    {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module A (M k)] [∀ k, Module (C k) (M k)]
    [∀ k, IsScalarTower A (C k) (M k)]
    {Mv : ι → κ → Type*} [∀ i k, AddCommGroup (Mv i k)] [∀ i k, Module A (Mv i k)]
    [∀ i k, Module (C k) (Mv i k)] [∀ i k, Module (D i k) (Mv i k)]
    [∀ i k, IsScalarTower A (C k) (Mv i k)] [∀ i k, IsScalarTower (C k) (D i k) (Mv i k)]
    (v : ∀ i k, B i →+* D i k) (ψ : ∀ i k, B i ⊗[A] C k ≃+* D i k)
    (hv : ∀ (i : ι) (k : κ) (b : B i), ψ i k (b ⊗ₜ[A] (1 : C k)) = v i k b)
    (hw : ∀ (i : ι) (k : κ) (c : C k), ψ i k ((1 : B i) ⊗ₜ[A] c) = algebraMap (C k) (D i k) c)
    (ρ : ∀ i k, M k →ₗ[C k] Mv i k)
    (hρ : ∀ i k, Function.Bijective ((ρ i k).liftBaseChange (D i k))) :
    ∃ e : (∀ i, B i) ⊗[A] (∀ k, M k) ≃ₗ[A] (∀ i k, Mv i k),
      ∀ (s : ∀ i, B i) (u : ∀ k, M k) (i : ι) (k : κ),
        e (s ⊗ₜ[A] u) i k = v i k (s i) • ρ i k (u k) := by
  classical
  have _ := Fintype.ofFinite ι
  have _ := Fintype.ofFinite κ
  have key : ∀ (i : ι) (k : κ), ∃ f : B i ⊗[A] M k ≃ₗ[A] Mv i k,
      ∀ (b : B i) (m : M k), f (b ⊗ₜ[A] m) = v i k b • ρ i k m := fun i k =>
    exists_cancelBaseChange A (B i) (C k) (D i k) (v i k) (ψ i k) (hv i k) (hw i k)
      (ρ i k) (hρ i k)
  choose F hF using key
  let split : (∀ i, B i) ⊗[A] (∀ k, M k) ≃ₗ[A] ∀ i k, B i ⊗[A] M k :=
    ((TensorProduct.comm A (∀ i, B i) (∀ k, M k)).trans
      ((TensorProduct.piRight A A (∀ k, M k) B).trans
        (LinearEquiv.piCongrRight fun i =>
          TensorProduct.comm A (∀ k, M k) (B i)))).trans
      (LinearEquiv.piCongrRight fun i => TensorProduct.piRight A A (B i) M)
  have hsplit : ∀ (s : ∀ i, B i) (u : ∀ k, M k) (i : ι) (k : κ),
      split (s ⊗ₜ[A] u) i k = s i ⊗ₜ[A] u k := fun _ _ _ _ => rfl
  refine ⟨split.trans
    (LinearEquiv.piCongrRight fun i => LinearEquiv.piCongrRight fun k => F i k),
    fun s u i k => ?_⟩
  change F i k (split (s ⊗ₜ[A] u) i k) = v i k (s i) • ρ i k (u k)
  rw [hsplit, hF]

/-- **A span over a product of rings restricts to a span over each factor.**  If a set of elements
of a product `∀ i, M i` of modules spans it over the product `∀ i, B i` of the acting rings, then
for each index the values of those elements at that index span the factor over its own ring.

The span condition a descent datum for a covering family produces is a span over the product of the
coefficient rings of the members, inside the product of the modules of sections; what a criterion
for being locally spanned by global sections asks for is the span at one member.  The passage is
this lemma: the action of the product is componentwise, so a representation of an element of the
product as a combination becomes, at one index, a representation of its value there, and every
element of a factor is the value at that index of an element of the product. -/
theorem span_pi_apply_eq_top {ι : Type*} (Bi : ι → Type*) [∀ i, Semiring (Bi i)]
    (Mi : ι → Type*) [∀ i, AddCommMonoid (Mi i)] [∀ i, Module (Bi i) (Mi i)]
    {S : Set (∀ i, Mi i)} (hS : Submodule.span (∀ i, Bi i) S = ⊤) (i : ι) :
    Submodule.span (Bi i) ((fun x => x i) '' S) = ⊤ := by
  classical
  have key : ∀ x ∈ Submodule.span (∀ j, Bi j) S,
      x i ∈ Submodule.span (Bi i) ((fun z : ∀ j, Mi j => z i) '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => exact zero_mem _
    | add z z' _ _ hz hz' => exact add_mem hz hz'
    | smul b z _ hz => exact Submodule.smul_mem _ (b i) hz
  refine Submodule.eq_top_iff'.2 fun y => ?_
  have hmem := key (Function.update (0 : ∀ j, Mi j) i y) (hS ▸ Submodule.mem_top)
  rwa [Function.update_self] at hmem

end Module.Descent

namespace SheafOfModules

universe uC vC r m

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A span over any ring acting through the sections of the structure sheaf is a span over those
sections.**  If the sections of `N` over `W` are spanned over a ring `B`, acting through a ring map
to the sections of the coefficient sheaf at `W`, by the restrictions along `f : W ⟶ V` of the
sections over `V`, then they are spanned by them over the sections of the coefficient sheaf, which
is `SheafOfModules.sectionSpan f = ⊤`.

This is `SheafOfModules.sectionSpan_eq_top_of_baseChangeEquiv` with the base change removed: only
that the sections are a `B`-span of the restrictions is used, not that they are a quotient of a
base change, and a span condition proved by descent over a product of coefficient rings arrives in
that weaker form. -/
theorem sectionSpan_eq_top_of_span_eq_top {V W : C} (f : W ⟶ V) (N : SheafOfModules.{m} R)
    (B : Type*) [Semiring B] [Module B (N.val.obj (op W))] (ψ : B →+* R.obj.obj (op W))
    (hψ : ∀ (b : B) (n : N.val.obj (op W)), b • n = ψ b • n)
    (hspan : _root_.Submodule.span B (Set.range (N.val.restrictₛₗ f.op)) = ⊤) :
    N.sectionSpan f = ⊤ := by
  refine _root_.Submodule.eq_top_iff'.2 fun n => ?_
  have hn : n ∈ _root_.Submodule.span B (Set.range (N.val.restrictₛₗ f.op)) :=
    _root_.Submodule.eq_top_iff'.1 hspan n
  induction hn using _root_.Submodule.span_induction with
  | mem y hy => exact _root_.Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y y' _ _ hy hy' => exact add_mem hy hy'
  | smul b y _ hy => rw [hψ]; exact _root_.Submodule.smul_mem _ _ hy

/-- **The sections over the members of a covering family are spanned by the restrictions of the
sections over the object covered, from a descent datum on their product.**

Let `g i : Y i ⟶ T` be a family, let the sections over `T` be a module over `A` and the sections
over `Y i` a module over `Bi i`, and let the product `∀ i, Bi i` be flat over `A`.  Suppose the
product of the modules of sections over the members carries a descent datum whose coaction and
whose unit map are described by two maps `p` and `q` through an injective comparison `e`, and that
every element on which `p` and `q` agree is a value of the map `ρ` of restrictions from `T`.  Then
the sections over each member are spanned, over the sections of the coefficient sheaf there, by
the restrictions of the sections over `T`.

The hypothesis `hmem` is the amalgamation half of the sheaf axiom for the family, read through the
comparison; `hρ` says that `ρ` is the map of restrictions; the flatness of the product is what a
covering family in the fppf topology provides, by
`AlgebraicGeometry.FibredSite.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage`.  The
conclusion is the hypothesis `hY` of
`AlgebraicGeometry.FibredSite.isGeneratedByUnit_over_of_sectionSpan_eq_top`.

Only one inclusion of the sheaf axiom is used, and neither injectivity of `ρ` nor the converse
inclusion: a span condition needs less than the base-change comparison, which is why this is
stated from `Module.Descent.span_range_eq_top_of_comparison` and not from
`Module.Descent.exists_baseChangeEquiv_of_comparison`. -/
theorem sectionSpan_eq_top_of_family_datum {T : C} {ι : Type*} {Y : ι → C} (g : ∀ i, Y i ⟶ T)
    (N : SheafOfModules.{m} R) (A : Type*) [CommRing A]
    (Bi : ι → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    [Module A (N.val.obj (op T))]
    [∀ i, Module A (N.val.obj (op (Y i)))] [∀ i, Module (Bi i) (N.val.obj (op (Y i)))]
    [∀ i, IsScalarTower A (Bi i) (N.val.obj (op (Y i)))]
    [Module.Flat A (∀ i, Bi i)]
    (d : Module.Descent.Datum A (∀ i, Bi i) (∀ i, N.val.obj (op (Y i))))
    {N₂ : Type*}
    (e : (∀ i, Bi i) ⊗[A] (∀ i, N.val.obj (op (Y i))) → N₂) (he : Function.Injective e)
    (p q : (∀ i, N.val.obj (op (Y i))) → N₂)
    (hp : ∀ u, p u = e (d.coaction u))
    (hq : ∀ u, q u = e ((1 : ∀ i, Bi i) ⊗ₜ[A] u))
    (ρ : N.val.obj (op T) →ₗ[A] ∀ i, N.val.obj (op (Y i)))
    (hρ : ∀ (n : N.val.obj (op T)) (i : ι), ρ n i = N.val.restrictₛₗ (g i).op n)
    (hmem : ∀ u, p u = q u → u ∈ LinearMap.range ρ)
    (ψ : ∀ i, Bi i →+* R.obj.obj (op (Y i)))
    (hψ : ∀ (i : ι) (b : Bi i) (n : N.val.obj (op (Y i))), b • n = ψ i b • n) (i : ι) :
    N.sectionSpan (g i) = ⊤ := by
  refine sectionSpan_eq_top_of_span_eq_top (g i) N (Bi i) (ψ i) (hψ i) ?_
  have h := Module.Descent.span_range_eq_top_of_comparison A (∀ i, Bi i) d e he p q hp hq ρ hmem
  have h2 := Module.Descent.span_pi_apply_eq_top Bi (fun i => N.val.obj (op (Y i))) h i
  have hset : (fun x : ∀ j, N.val.obj (op (Y j)) => x i) '' Set.range ρ
      = Set.range (N.val.restrictₛₗ (g i).op) := by
    ext z
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    exact exists_congr fun n => by rw [hρ]
  rwa [hset] at h2

end SheafOfModules

end
