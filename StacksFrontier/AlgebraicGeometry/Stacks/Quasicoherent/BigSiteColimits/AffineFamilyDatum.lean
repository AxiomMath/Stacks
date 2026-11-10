module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDescentSpan
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FiniteDisjointSections

/-!
# The descent datum carried by the sections over a covering family

A descent datum relative to a covering *family* `{Y i ⟶ T}` is a descent datum relative to the
single ring map `A → ∀ i, B i` into the product of the coefficient rings of the members, on the
product `∀ i, N(Y i)` of the modules of sections.  No coproduct is formed inside the site: the
double overlaps `Pb i j` and the triple overlaps `Pb₃ i j k` enter only through the products
`∀ i j, N(Pb i j)` and `∀ i j k, N(Pb₃ i j k)`, which play the roles of the two auxiliary groups
of `Module.Descent.exists_datum_of_comparison`.  That engine is stated for arbitrary groups in
those two slots, so the family case is an instantiation of it and not a second development.

Every hypothesis of the engine is discharged here componentwise.  The coaction is restriction
along the first projection of the double overlap, its retraction is restriction along the
diagonal, and the two maps into the sections over the triple overlaps are restrictions along two
of its three projections; each compatibility is then functoriality of restriction
(`PresheafOfModules.restrictₛₗ_restrictₛₗ_op`) together with one commutation of the overlaps, in
exactly the way `PresheafOfModules.exists_datum_of_baseChange` discharges them for a single
covering morphism.  No finiteness of the index type is used: it is needed to *build* the two
comparisons, not to assemble the datum from them.

The two comparisons are built by cancelling a base change member by member.  The one on the
double overlaps is `Module.Descent.exists_cancelBaseChange_pi` at the family of coefficient rings
of the members; the one on the triple overlaps is the same statement one degree up, at the family
of coefficient rings of the double overlaps, composed with the first comparison tensored with the
product.  The second application is indexed by a sigma type over the index type rather than by a
product of it, which is what lets `LinearEquiv.piCurry` transport between `∀ i j, _` and
`∀ q : Σ _, _, _` without an auxiliary equivalence; the `A`-linearity of the conclusion of
`Module.Descent.exists_cancelBaseChange_pi`, rather than mere additivity, is what makes tensoring
the first comparison with the product available.

The remaining input is the amalgamation half of the sheaf axiom.  For a sheaf of modules it is
`SheafOfModules.isSheafFor_ofArrows`, so what is owed is only the translation of a compatible
family of elements into the locus where the two restrictions to the overlaps agree: a pair of
arrows into two members agreeing over the object covered factors through the fibre product of
those two members, and the compatibility of the family is then the equality of the two
restrictions to that fibre product.

## Main results

* `Module.Descent.exists_cancelBaseChange_pi_pair`: **the two comparisons of a family descent
  datum at once**, the second characterised in terms of the first, from the member-wise
  base-change comparisons over the double and the triple overlaps.
* `PresheafOfModules.exists_family_datum_of_baseChange`: **the descent datum carried by the
  product of the modules of sections over the members of a covering family**, with its coaction
  characterised as restriction along the first projection of the double overlaps.
* `SheafOfModules.exists_restrictₛₗ_eq_of_pairwise_eq`: **a family of sections agreeing on the
  double overlaps is the family of restrictions of a single section**, which is the amalgamation
  half of the sheaf axiom in the form the descent datum consumes.
* `SheafOfModules.sectionSpan_eq_top_of_family_baseChange`: **the sections over each member of a
  covering family are spanned by the restrictions of the sections over the object covered**, from
  the two comparisons, the overlaps and flatness of the product of the coefficient rings.
* `SheafOfModules.sectionSpan_eq_top_of_family_cancelBaseChange`: the same from the *member-wise*
  base-change comparisons over the double and the triple overlaps, which is what a module
  presented on the slice at each member of the family provides.

## Implementation notes

The comparison on the double overlaps is assumed additive and its values on pure tensors are
given, rather than it being assumed semilinear: the two restrictions it is compared with are
semilinear along two different ring maps, so there is no single ring over which it could be read
as a linear map.  Its semilinearity for the action of the product of the coefficient rings is
derived from its values, by induction on the tensor product, and is the one place where that
induction occurs.

The maps out of the products are built as bundled additive maps with their application lemmas
stated as `rfl` lemmas immediately afterwards, so that every subsequent step is a rewrite rather
than an unfolding.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe y z v u

namespace Module.Descent

/-- **The two comparisons of a family descent datum at once, the second characterised through the
first.**  Let `{Y i}` be a finite family with coefficient rings `B i`, let `D i j` be the
coefficient ring of the double overlap of the `i`-th and `j`-th members and `D₃ i j k` that of a
triple overlap, each identified with a tensor product by a ring isomorphism whose values on pure
tensors are given by the explicit maps `v i j` and `u i j k` and by the structural maps.  Let the
`D i j`-module `Mv i j` be the base change of the `B j`-module `M j` and the `D₃ i j k`-module
`Mv₃ i j k` the base change of `Mv j k`.  Then there are an additive identification
`(∀ i, B i) ⊗[A] (∀ i, M i) ≃+ ∀ i j, Mv i j` and an injection
`(∀ i, B i) ⊗[A] ((∀ i, B i) ⊗[A] (∀ i, M i)) →+ ∀ i j k, Mv₃ i j k` whose values on pure tensors
are `v i j (s i) • ρ i j (m j)` and `u i j k (s i) • ρ₃ i j k (e y j k)`.

This is the shape `PresheafOfModules.exists_family_datum_of_baseChange` takes its two comparisons
in: the hypothesis characterising the second one refers to the first, so the two must be produced
by a single statement.

The second application of `Module.Descent.exists_cancelBaseChange_pi` is indexed by `Σ _ : ι, ι`
rather than by `ι × ι`, which is what makes `LinearEquiv.piCurry` the transport between
`∀ i j, _` and the product over that index; with a product index an auxiliary equivalence would
have to be built first.  Only one family of `Algebra` instances is assumed at each level, the
other inclusion being the explicit `v` or `u`, so the diagonal `i = j` of a self-product remains
admissible. -/
theorem exists_cancelBaseChange_pi_pair
    (A : Type*) [CommRing A] {ι : Type*} [Finite ι]
    (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (D : ι → ι → Type*) [∀ i j, CommRing (D i j)] [∀ i j, Algebra A (D i j)]
    [∀ i j, Algebra (B j) (D i j)]
    (D₃ : ι → ι → ι → Type*) [∀ i j k, CommRing (D₃ i j k)]
    [∀ i j k, Algebra (D j k) (D₃ i j k)]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, Module (B i) (M i)]
    [∀ i, IsScalarTower A (B i) (M i)]
    {Mv : ι → ι → Type*} [∀ i j, AddCommGroup (Mv i j)] [∀ i j, Module A (Mv i j)]
    [∀ i j, Module (B j) (Mv i j)] [∀ i j, Module (D i j) (Mv i j)]
    [∀ i j, IsScalarTower A (B j) (Mv i j)] [∀ i j, IsScalarTower (B j) (D i j) (Mv i j)]
    [∀ i j, IsScalarTower A (D i j) (Mv i j)]
    {Mv₃ : ι → ι → ι → Type*} [∀ i j k, AddCommGroup (Mv₃ i j k)]
    [∀ i j k, Module A (Mv₃ i j k)] [∀ i j k, Module (D j k) (Mv₃ i j k)]
    [∀ i j k, Module (D₃ i j k) (Mv₃ i j k)]
    [∀ i j k, IsScalarTower A (D j k) (Mv₃ i j k)]
    [∀ i j k, IsScalarTower (D j k) (D₃ i j k) (Mv₃ i j k)]
    (v : ∀ i j, B i →+* D i j) (ψ : ∀ i j, B i ⊗[A] B j ≃+* D i j)
    (hv : ∀ (i j : ι) (b : B i), ψ i j (b ⊗ₜ[A] (1 : B j)) = v i j b)
    (hw : ∀ (i j : ι) (c : B j), ψ i j ((1 : B i) ⊗ₜ[A] c) = algebraMap (B j) (D i j) c)
    (u : ∀ i j k, B i →+* D₃ i j k) (ψ₃ : ∀ i j k, B i ⊗[A] D j k ≃+* D₃ i j k)
    (hu : ∀ (i j k : ι) (b : B i), ψ₃ i j k (b ⊗ₜ[A] (1 : D j k)) = u i j k b)
    (hw₃ : ∀ (i j k : ι) (d : D j k),
      ψ₃ i j k ((1 : B i) ⊗ₜ[A] d) = algebraMap (D j k) (D₃ i j k) d)
    (ρ : ∀ i j, M j →ₗ[B j] Mv i j)
    (hρ : ∀ i j, Function.Bijective ((ρ i j).liftBaseChange (D i j)))
    (ρ₃ : ∀ i j k, Mv j k →ₗ[D j k] Mv₃ i j k)
    (hρ₃ : ∀ i j k, Function.Bijective ((ρ₃ i j k).liftBaseChange (D₃ i j k))) :
    ∃ (e : (∀ i, B i) ⊗[A] (∀ i, M i) ≃+ ∀ i j, Mv i j)
      (e₃ : (∀ i, B i) ⊗[A] ((∀ i, B i) ⊗[A] (∀ i, M i)) →+ ∀ i j k, Mv₃ i j k),
      (∀ (s : ∀ i, B i) (m : ∀ i, M i) (i j : ι),
          e (s ⊗ₜ[A] m) i j = v i j (s i) • ρ i j (m j)) ∧
        Function.Injective e₃ ∧
        ∀ (s : ∀ i, B i) (y : (∀ i, B i) ⊗[A] (∀ i, M i)) (i j k : ι),
          e₃ (s ⊗ₜ[A] y) i j k = u i j k (s i) • ρ₃ i j k (e y j k) := by
  obtain ⟨e, he⟩ := exists_cancelBaseChange_pi A B B D v ψ hv hw ρ hρ
  obtain ⟨f, hf⟩ := exists_cancelBaseChange_pi A B (fun q : Σ _ : ι, ι => D q.1 q.2)
    (fun i q => D₃ i q.1 q.2) (fun i q => u i q.1 q.2) (fun i q => ψ₃ i q.1 q.2)
    (fun i q => hu i q.1 q.2) (fun i q => hw₃ i q.1 q.2)
    (fun i q => ρ₃ i q.1 q.2) (fun i q => hρ₃ i q.1 q.2)
  let cur : (∀ i j, Mv i j) ≃ₗ[A] ∀ q : Σ _ : ι, ι, Mv q.1 q.2 :=
    (LinearEquiv.piCurry A fun i j => Mv i j).symm
  let cur₃ : (∀ (i : ι) (q : Σ _ : ι, ι), Mv₃ i q.1 q.2) ≃ₗ[A] ∀ i j k, Mv₃ i j k :=
    LinearEquiv.piCongrRight fun i => LinearEquiv.piCurry A fun j k => Mv₃ i j k
  refine ⟨e.toAddEquiv, ((TensorProduct.congr (LinearEquiv.refl A (∀ i, B i))
      (e.trans cur)).trans (f.trans cur₃)).toAddMonoidHom, he, ?_, fun s y i j k => ?_⟩
  · exact ((TensorProduct.congr (LinearEquiv.refl A (∀ i, B i))
      (e.trans cur)).trans (f.trans cur₃)).injective
  · change cur₃ (f (TensorProduct.congr (LinearEquiv.refl A (∀ i, B i)) (e.trans cur)
      (s ⊗ₜ[A] y))) i j k = _
    rw [TensorProduct.congr_tmul]
    exact hf s (cur (e y)) i ⟨j, k⟩

end Module.Descent

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{z}}

/-- **The descent datum carried by the product of the modules of sections over the members of a
covering family.**

Let `{Y i}` be a family of objects, let `Pb i j` carry two projections `pr₁ i j` and `pr₂ i j` to
the `i`-th and the `j`-th member and `Pb₃ i j k` three projections `t₁₂`, `t₁₃`, `t₂₃` to the
double overlaps, and let `δ i` be a diagonal of `Pb i i`.  Let the sections over `Y i` be a module
over a commutative ring `Bi i` which is an algebra over a commutative ring `A`, let `D i j` and
`D₃ i j k` act on the sections over the overlaps, and let `v₁`, `u₁`, `w₁₂`, `w₁₃` and `wδ` be the
ring maps along which restriction is semilinear.  Suppose the comparison `e` on the double
overlaps carries `s ⊗ₜ u` at the slot `(i, j)` to `v₁ i j (s i) • (restriction of u j along
pr₂ i j)` and the injection `e₃` on the triple overlaps carries `s ⊗ₜ y` at `(i, j, k)` to
`u₁ i j k (s i) • (restriction of e y j k along t₂₃ i j k)`.  Then the product of the modules of
sections over the members carries a descent datum relative to `A → ∀ i, Bi i`, whose coaction is
restriction along the first projections of the double overlaps.

Every hypothesis is either a commutation of the overlaps, a factorisation of the identity through
a diagonal, an identity between the induced ring maps, or semilinearity of restriction along one
arrow; the five commutations are the ones
`AlgebraicGeometry.FibredSite.exists_affine_triple_self_product` returns, taken at a pair and at a
triple of members.  No finiteness of the index type is used: it enters only in the construction of
the two comparisons, in
`Module.Descent.exists_cancelBaseChange_pi_pair`.

This is the family analogue of `PresheafOfModules.exists_datum_of_baseChange`, obtained from the
same engine `Module.Descent.exists_datum_of_comparison`, which is stated for arbitrary groups in
the two auxiliary slots precisely so that both instantiations are available. -/
theorem exists_family_datum_of_baseChange {N : PresheafOfModules.{y} R}
    {ι : Type*} {Y : ι → C} {Pb : ι → ι → C} {Pb₃ : ι → ι → ι → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
    (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j) (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k)
    (hδ₁ : ∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) (hδ₂ : ∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i))
    (hc₁ : ∀ i j k, t₁₂ i j k ≫ pr₁ i j = t₁₃ i j k ≫ pr₁ i k)
    (hc₂ : ∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k)
    (hc₃ : ∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k)
    (A : Type*) [CommRing A] (Bi : ι → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (D : ι → ι → Type*) [∀ i j, CommRing (D i j)]
    (D₃ : ι → ι → ι → Type*) [∀ i j k, CommRing (D₃ i j k)]
    [∀ i, Module A (N.obj (op (Y i)))] [∀ i, Module (Bi i) (N.obj (op (Y i)))]
    [∀ i, IsScalarTower A (Bi i) (N.obj (op (Y i)))]
    [∀ i j, Module (D i j) (N.obj (op (Pb i j)))]
    [∀ i j k, Module (D₃ i j k) (N.obj (op (Pb₃ i j k)))]
    (v₁ : ∀ i j, Bi i →+* D i j) (u₁ : ∀ i j k, Bi i →+* D₃ i j k)
    (w₁₂ : ∀ i j k, D i j →+* D₃ i j k) (w₁₃ : ∀ i j k, D i k →+* D₃ i j k)
    (wδ : ∀ i, D i i →+* Bi i)
    (hwδ : ∀ (i : ι) (b : Bi i), wδ i (v₁ i i b) = b)
    (h₁₂ : ∀ (i j k : ι) (b : Bi i), w₁₂ i j k (v₁ i j b) = u₁ i j k b)
    (h₁₃ : ∀ (i j k : ι) (b : Bi i), w₁₃ i j k (v₁ i k b) = u₁ i j k b)
    (hsmq₁ : ∀ (i j : ι) (b : Bi i) (n : N.obj (op (Y i))),
      N.restrictₛₗ (pr₁ i j).op (b • n) = v₁ i j b • N.restrictₛₗ (pr₁ i j).op n)
    (hsmδ : ∀ (i : ι) (d : D i i) (w : N.obj (op (Pb i i))),
      N.restrictₛₗ (δ i).op (d • w) = wδ i d • N.restrictₛₗ (δ i).op w)
    (hsm₁₂ : ∀ (i j k : ι) (d : D i j) (w : N.obj (op (Pb i j))),
      N.restrictₛₗ (t₁₂ i j k).op (d • w) = w₁₂ i j k d • N.restrictₛₗ (t₁₂ i j k).op w)
    (hsm₁₃ : ∀ (i j k : ι) (d : D i k) (w : N.obj (op (Pb i k))),
      N.restrictₛₗ (t₁₃ i j k).op (d • w) = w₁₃ i j k d • N.restrictₛₗ (t₁₃ i j k).op w)
    (e : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i))) ≃+ ∀ i j, N.obj (op (Pb i j)))
    (he : ∀ (s : ∀ i, Bi i) (uu : ∀ i, N.obj (op (Y i))) (i j : ι),
      e (s ⊗ₜ[A] uu) i j = v₁ i j (s i) • N.restrictₛₗ (pr₂ i j).op (uu j))
    (e₃ : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))) →+
      ∀ i j k, N.obj (op (Pb₃ i j k)))
    (he₃ : Function.Injective e₃)
    (he₃tmul : ∀ (s : ∀ i, Bi i) (y : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))) (i j k : ι),
      e₃ (s ⊗ₜ[A] y) i j k = u₁ i j k (s i) • N.restrictₛₗ (t₂₃ i j k).op (e y j k)) :
    ∃ d : Module.Descent.Datum A (∀ i, Bi i) (∀ i, N.obj (op (Y i))),
      ∀ (uu : ∀ i, N.obj (op (Y i))) (i j : ι),
        e (d.coaction uu) i j = N.restrictₛₗ (pr₁ i j).op (uu i) := by
  let P : (∀ i, N.obj (op (Y i))) →+ ∀ i j, N.obj (op (Pb i j)) :=
    .mk' (fun uu i j => N.restrictₛₗ (pr₁ i j).op (uu i))
      fun _ _ => by funext i j; exact map_add _ _ _
  have hPapp : ∀ (uu : ∀ i, N.obj (op (Y i))) (i j : ι),
      P uu i j = N.restrictₛₗ (pr₁ i j).op (uu i) := fun _ _ _ => rfl
  let U : (∀ i j, N.obj (op (Pb i j))) →+ ∀ i j k, N.obj (op (Pb₃ i j k)) :=
    .mk' (fun w i j k => N.restrictₛₗ (t₁₂ i j k).op (w i j))
      fun _ _ => by funext i j k; exact map_add _ _ _
  have hUapp : ∀ (w : ∀ i j, N.obj (op (Pb i j))) (i j k : ι),
      U w i j k = N.restrictₛₗ (t₁₂ i j k).op (w i j) := fun _ _ _ _ => rfl
  let V : (∀ i j, N.obj (op (Pb i j))) →+ ∀ i j k, N.obj (op (Pb₃ i j k)) :=
    .mk' (fun w i j k => N.restrictₛₗ (t₁₃ i j k).op (w i k))
      fun _ _ => by funext i j k; exact map_add _ _ _
  have hVapp : ∀ (w : ∀ i j, N.obj (op (Pb i j))) (i j k : ι),
      V w i j k = N.restrictₛₗ (t₁₃ i j k).op (w i k) := fun _ _ _ _ => rfl
  have hes : ∀ (s : ∀ i, Bi i) (y : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))) (i j : ι),
      e (s • y) i j = v₁ i j (s i) • e y i j := by
    intro s y
    induction y with
    | tmul t uu =>
      intro i j
      rw [TensorProduct.smul_tmul', smul_eq_mul, he, he, Pi.mul_apply, map_mul, mul_smul]
    | add y y' hy hy' =>
      intro i j
      rw [smul_add, map_add]
      simp only [Pi.add_apply]
      rw [hy, hy', map_add]
      simp only [Pi.add_apply]
      rw [smul_add]
  have hyc : ∀ (uu : ∀ i, N.obj (op (Y i)))
      (y : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))), P uu = e y →
      ∀ i j, e y i j = N.restrictₛₗ (pr₁ i j).op (uu i) := fun uu y hy i j => by
    rw [← hy, hPapp]
  have hesm : ∀ (s : ∀ i, Bi i) (uu : ∀ i, N.obj (op (Y i)))
      (y : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))), P uu = e y → P (s • uu) = e (s • y) := by
    intro s uu y hy
    funext i j
    rw [hPapp, hes, hyc uu y hy]
    exact hsmq₁ i j (s i) (uu i)
  have hrp : ∀ (uu : ∀ i, N.obj (op (Y i))) (i : ι),
      N.restrictₛₗ (δ i).op (P uu i i) = uu i := by
    intro uu i
    rw [hPapp, N.restrictₛₗ_restrictₛₗ_op, hδ₁]
    simp
  have hrec : ∀ (x : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))) (i : ι),
      N.restrictₛₗ (δ i).op (e x i i) =
        Module.Descent.counit A (∀ i, Bi i) (∀ i, N.obj (op (Y i))) x i := by
    intro x
    induction x with
    | tmul s uu =>
      intro i
      rw [he, hsmδ, hwδ, N.restrictₛₗ_restrictₛₗ_op, hδ₂, Module.Descent.counit_tmul]
      simp
    | add x x' hx hx' =>
      intro i
      simp only [map_add, Pi.add_apply]
      rw [hx, hx']
  have hu : ∀ (s : ∀ i, Bi i) (uu : ∀ i, N.obj (op (Y i)))
      (y : (∀ i, Bi i) ⊗[A] (∀ i, N.obj (op (Y i)))), P uu = e y →
      e₃ (s ⊗ₜ[A] y) = U (e (s ⊗ₜ[A] uu)) := by
    intro s uu y hy
    funext i j k
    rw [hUapp, he₃tmul, hyc uu y hy, N.restrictₛₗ_restrictₛₗ_op, he, hsm₁₂, h₁₂,
      N.restrictₛₗ_restrictₛₗ_op, hc₂]
  have hv : ∀ (s : ∀ i, Bi i) (uu : ∀ i, N.obj (op (Y i))),
      e₃ (s ⊗ₜ[A] ((1 : ∀ i, Bi i) ⊗ₜ[A] uu)) = V (e (s ⊗ₜ[A] uu)) := by
    intro s uu
    funext i j k
    rw [hVapp, he₃tmul, he, Pi.one_apply, map_one, one_smul, N.restrictₛₗ_restrictₛₗ_op, he,
      hsm₁₃, h₁₃, N.restrictₛₗ_restrictₛₗ_op, hc₃]
  have huv : ∀ uu : ∀ i, N.obj (op (Y i)), U (P uu) = V (P uu) := by
    intro uu
    funext i j k
    rw [hUapp, hVapp, hPapp, hPapp, N.restrictₛₗ_restrictₛₗ_op, N.restrictₛₗ_restrictₛₗ_op, hc₁]
  obtain ⟨d, hd⟩ := Module.Descent.exists_datum_of_comparison A (∀ i, Bi i) e P hesm
    (fun w i => N.restrictₛₗ (δ i).op (w i i)) (fun uu => funext (hrp uu))
    (fun x => funext (hrec x)) e₃ he₃ U V hu hv huv
  exact ⟨d, fun uu i j => by rw [hd uu, hPapp]⟩

end PresheafOfModules

namespace SheafOfModules

universe w uC vC r m

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A family of sections over the members of a covering family which agree on the double
overlaps is the family of restrictions of a single section.**

This is the amalgamation half of the sheaf axiom for the family, in the form the descended module
of a family descent datum is cut out by: the locus where the two restrictions to the overlaps
agree.  The translation is that a pair of arrows into two members which agree over the object
covered factors through the fibre product of those two members, by its universal property, so the
compatibility asked of a family of elements is implied by the equality of the two restrictions to
each fibre product.

Nothing is assumed affine, quasi-compact or finite, and the sheaf axiom used is
`SheafOfModules.isSheafFor_ofArrows`, which is `N.cond` read for a family of arrows.  Only the
existence half is concluded; the uniqueness half is
`SheafOfModules.injective_restrict`. -/
theorem exists_restrictₛₗ_eq_of_pairwise_eq (N : SheafOfModules.{m} R) {T : C} {ι : Type w}
    {Y : ι → C} (g : ∀ i, Y i ⟶ T) {Pb : ι → ι → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j)
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j))
    (hcov : Sieve.ofArrows Y g ∈ J T) (uu : ∀ i, N.val.obj (op (Y i)))
    (hagree : ∀ i j, N.val.restrictₛₗ (pr₁ i j).op (uu i) =
      N.val.restrictₛₗ (pr₂ i j).op (uu j)) :
    ∃ n : N.val.obj (op T), ∀ i, N.val.restrictₛₗ (g i).op n = uu i := by
  have hcompat : Presieve.Arrows.Compatible
      (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) g uu := by
    intro i j Z gi gj hcomm
    have h₁ : N.val.restrictₛₗ gi.op (uu i) =
        N.val.restrictₛₗ ((hpb i j).lift gi gj hcomm).op
          (N.val.restrictₛₗ (pr₁ i j).op (uu i)) := by
      rw [N.val.restrictₛₗ_restrictₛₗ_op, (hpb i j).lift_fst]
    have h₂ : N.val.restrictₛₗ gj.op (uu j) =
        N.val.restrictₛₗ ((hpb i j).lift gi gj hcomm).op
          (N.val.restrictₛₗ (pr₂ i j).op (uu j)) := by
      rw [N.val.restrictₛₗ_restrictₛₗ_op, (hpb i j).lift_snd]
    exact h₁.trans ((congrArg _ (hagree i j)).trans h₂.symm)
  obtain ⟨n, hn, -⟩ := (Presieve.isSheafFor_arrows_iff _ g).1
    (N.isSheafFor_ofArrows g hcov) uu hcompat
  exact ⟨n, hn⟩

/-- **The sections over each member of a covering family are spanned by the restrictions of the
sections over the object covered**, from the two base-change comparisons on the overlaps and
flatness of the product of the coefficient rings of the members.

This composes `PresheafOfModules.exists_family_datum_of_baseChange`,
`SheafOfModules.exists_restrictₛₗ_eq_of_pairwise_eq` and
`SheafOfModules.sectionSpan_eq_top_of_family_datum`: the descent datum cuts out its descended
module as the locus where the two restrictions to the double overlaps agree, the sheaf axiom says
that locus consists of restrictions from the object covered, and flat descent turns that into a
span condition over the product of the coefficient rings, read off at a single member.

The conclusion is the hypothesis `hY` of
`AlgebraicGeometry.FibredSite.isGeneratedByUnit_over_of_sectionSpan_eq_top`.  Only one inclusion
of the sheaf axiom is used, and neither injectivity of the restriction from the object covered nor
the converse inclusion: a span condition needs strictly less than the base-change comparison. -/
theorem sectionSpan_eq_top_of_family_baseChange (N : SheafOfModules.{m} R)
    {T : C} {ι : Type w} {Y : ι → C} (g : ∀ i, Y i ⟶ T)
    {Pb : ι → ι → C} {Pb₃ : ι → ι → ι → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
    (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j) (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k)
    (hδ₁ : ∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) (hδ₂ : ∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i))
    (hc₁ : ∀ i j k, t₁₂ i j k ≫ pr₁ i j = t₁₃ i j k ≫ pr₁ i k)
    (hc₂ : ∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k)
    (hc₃ : ∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k)
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j))
    (hcov : Sieve.ofArrows Y g ∈ J T)
    (A : Type*) [CommRing A] (Bi : ι → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (D : ι → ι → Type*) [∀ i j, CommRing (D i j)]
    (D₃ : ι → ι → ι → Type*) [∀ i j k, CommRing (D₃ i j k)]
    [Module A (N.val.obj (op T))]
    [∀ i, Module A (N.val.obj (op (Y i)))] [∀ i, Module (Bi i) (N.val.obj (op (Y i)))]
    [∀ i, IsScalarTower A (Bi i) (N.val.obj (op (Y i)))]
    [∀ i j, Module (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j k, Module (D₃ i j k) (N.val.obj (op (Pb₃ i j k)))]
    [Module.Flat A (∀ i, Bi i)]
    (v₁ : ∀ i j, Bi i →+* D i j) (u₁ : ∀ i j k, Bi i →+* D₃ i j k)
    (w₁₂ : ∀ i j k, D i j →+* D₃ i j k) (w₁₃ : ∀ i j k, D i k →+* D₃ i j k)
    (wδ : ∀ i, D i i →+* Bi i)
    (hwδ : ∀ (i : ι) (b : Bi i), wδ i (v₁ i i b) = b)
    (h₁₂ : ∀ (i j k : ι) (b : Bi i), w₁₂ i j k (v₁ i j b) = u₁ i j k b)
    (h₁₃ : ∀ (i j k : ι) (b : Bi i), w₁₃ i j k (v₁ i k b) = u₁ i j k b)
    (hsmq₁ : ∀ (i j : ι) (b : Bi i) (n : N.val.obj (op (Y i))),
      N.val.restrictₛₗ (pr₁ i j).op (b • n) = v₁ i j b • N.val.restrictₛₗ (pr₁ i j).op n)
    (hsmδ : ∀ (i : ι) (d : D i i) (w : N.val.obj (op (Pb i i))),
      N.val.restrictₛₗ (δ i).op (d • w) = wδ i d • N.val.restrictₛₗ (δ i).op w)
    (hsm₁₂ : ∀ (i j k : ι) (d : D i j) (w : N.val.obj (op (Pb i j))),
      N.val.restrictₛₗ (t₁₂ i j k).op (d • w) =
        w₁₂ i j k d • N.val.restrictₛₗ (t₁₂ i j k).op w)
    (hsm₁₃ : ∀ (i j k : ι) (d : D i k) (w : N.val.obj (op (Pb i k))),
      N.val.restrictₛₗ (t₁₃ i j k).op (d • w) =
        w₁₃ i j k d • N.val.restrictₛₗ (t₁₃ i j k).op w)
    (e : (∀ i, Bi i) ⊗[A] (∀ i, N.val.obj (op (Y i))) ≃+ ∀ i j, N.val.obj (op (Pb i j)))
    (he : ∀ (s : ∀ i, Bi i) (uu : ∀ i, N.val.obj (op (Y i))) (i j : ι),
      e (s ⊗ₜ[A] uu) i j = v₁ i j (s i) • N.val.restrictₛₗ (pr₂ i j).op (uu j))
    (e₃ : (∀ i, Bi i) ⊗[A] ((∀ i, Bi i) ⊗[A] (∀ i, N.val.obj (op (Y i)))) →+
      ∀ i j k, N.val.obj (op (Pb₃ i j k)))
    (he₃ : Function.Injective e₃)
    (he₃tmul : ∀ (s : ∀ i, Bi i) (y : (∀ i, Bi i) ⊗[A] (∀ i, N.val.obj (op (Y i))))
      (i j k : ι),
      e₃ (s ⊗ₜ[A] y) i j k = u₁ i j k (s i) • N.val.restrictₛₗ (t₂₃ i j k).op (e y j k))
    (ρ : N.val.obj (op T) →ₗ[A] ∀ i, N.val.obj (op (Y i)))
    (hρ : ∀ (n : N.val.obj (op T)) (i : ι), ρ n i = N.val.restrictₛₗ (g i).op n)
    (ψ : ∀ i, Bi i →+* R.obj.obj (op (Y i)))
    (hψ : ∀ (i : ι) (b : Bi i) (n : N.val.obj (op (Y i))), b • n = ψ i b • n) (i : ι) :
    N.sectionSpan (g i) = ⊤ := by
  obtain ⟨d, hd⟩ := PresheafOfModules.exists_family_datum_of_baseChange pr₁ pr₂ δ t₁₂ t₁₃ t₂₃
    hδ₁ hδ₂ hc₁ hc₂ hc₃ A Bi D D₃ v₁ u₁ w₁₂ w₁₃ wδ hwδ h₁₂ h₁₃ hsmq₁ hsmδ hsm₁₂ hsm₁₃
    e he e₃ he₃ he₃tmul
  refine sectionSpan_eq_top_of_family_datum g N A Bi d e e.injective
    (fun uu a b => N.val.restrictₛₗ (pr₁ a b).op (uu a))
    (fun uu => e ((1 : ∀ i, Bi i) ⊗ₜ[A] uu))
    (fun uu => funext fun a => funext fun b => (hd uu a b).symm) (fun _ => rfl) ρ hρ ?_ ψ hψ i
  intro uu hpq
  have hagree : ∀ a b, N.val.restrictₛₗ (pr₁ a b).op (uu a) =
      N.val.restrictₛₗ (pr₂ a b).op (uu b) := by
    intro a b
    have hab : N.val.restrictₛₗ (pr₁ a b).op (uu a) =
        e ((1 : ∀ i, Bi i) ⊗ₜ[A] uu) a b := congrFun (congrFun hpq a) b
    rwa [he, Pi.one_apply, map_one, one_smul] at hab
  obtain ⟨n, hn⟩ := N.exists_restrictₛₗ_eq_of_pairwise_eq g pr₁ pr₂ hpb hcov uu hagree
  exact ⟨n, funext fun a => (hρ n a).trans (hn a)⟩

/-- **The sections over each member of a covering family are spanned by the restrictions of the
sections over the object covered**, from the member-wise base-change comparisons over the
overlaps.

This is `SheafOfModules.sectionSpan_eq_top_of_family_baseChange` with its two comparisons supplied
by `Module.Descent.exists_cancelBaseChange_pi_pair`, so that what is asked for is exactly what a
module presented on the slice at each member provides: for each pair of members, the sections over
their double overlap are the base change of the sections over the second along the ring map of the
second projection, and likewise one degree up over the triple overlaps.  Everything else is the
geometry of the overlaps — the two factorisations of the identity through a diagonal, the three
commutations of a triple overlap, the fibre product squares, and the ring isomorphisms exhibiting
the coefficient ring of an overlap as a tensor product.

The index type is finite because the comparisons are built through
`TensorProduct.piRight`, which commutes a tensor product past a product of modules only over a
finite index; the datum itself needs no finiteness, by
`PresheafOfModules.exists_family_datum_of_baseChange`. -/
theorem sectionSpan_eq_top_of_family_cancelBaseChange (N : SheafOfModules.{m} R)
    {T : C} {ι : Type w} [Finite ι] {Y : ι → C} (g : ∀ i, Y i ⟶ T)
    {Pb : ι → ι → C} {Pb₃ : ι → ι → ι → C}
    (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j) (δ : ∀ i, Y i ⟶ Pb i i)
    (t₁₂ : ∀ i j k, Pb₃ i j k ⟶ Pb i j) (t₁₃ : ∀ i j k, Pb₃ i j k ⟶ Pb i k)
    (t₂₃ : ∀ i j k, Pb₃ i j k ⟶ Pb j k)
    (hδ₁ : ∀ i, δ i ≫ pr₁ i i = 𝟙 (Y i)) (hδ₂ : ∀ i, δ i ≫ pr₂ i i = 𝟙 (Y i))
    (hc₁ : ∀ i j k, t₁₂ i j k ≫ pr₁ i j = t₁₃ i j k ≫ pr₁ i k)
    (hc₂ : ∀ i j k, t₁₂ i j k ≫ pr₂ i j = t₂₃ i j k ≫ pr₁ j k)
    (hc₃ : ∀ i j k, t₁₃ i j k ≫ pr₂ i k = t₂₃ i j k ≫ pr₂ j k)
    (hpb : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j))
    (hcov : Sieve.ofArrows Y g ∈ J T)
    (A : Type*) [CommRing A] (Bi : ι → Type*) [∀ i, CommRing (Bi i)] [∀ i, Algebra A (Bi i)]
    (D : ι → ι → Type*) [∀ i j, CommRing (D i j)] [∀ i j, Algebra A (D i j)]
    [∀ i j, Algebra (Bi j) (D i j)]
    (D₃ : ι → ι → ι → Type*) [∀ i j k, CommRing (D₃ i j k)]
    [∀ i j k, Algebra (D j k) (D₃ i j k)]
    [Module A (N.val.obj (op T))]
    [∀ i, Module A (N.val.obj (op (Y i)))] [∀ i, Module (Bi i) (N.val.obj (op (Y i)))]
    [∀ i, IsScalarTower A (Bi i) (N.val.obj (op (Y i)))]
    [∀ i j, Module A (N.val.obj (op (Pb i j)))] [∀ i j, Module (Bi j) (N.val.obj (op (Pb i j)))]
    [∀ i j, Module (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j, IsScalarTower A (Bi j) (N.val.obj (op (Pb i j)))]
    [∀ i j, IsScalarTower (Bi j) (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j, IsScalarTower A (D i j) (N.val.obj (op (Pb i j)))]
    [∀ i j k, Module A (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, Module (D j k) (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, Module (D₃ i j k) (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, IsScalarTower A (D j k) (N.val.obj (op (Pb₃ i j k)))]
    [∀ i j k, IsScalarTower (D j k) (D₃ i j k) (N.val.obj (op (Pb₃ i j k)))]
    [Module.Flat A (∀ i, Bi i)]
    (v₁ : ∀ i j, Bi i →+* D i j) (ψ : ∀ i j, Bi i ⊗[A] Bi j ≃+* D i j)
    (hv : ∀ (i j : ι) (b : Bi i), ψ i j (b ⊗ₜ[A] (1 : Bi j)) = v₁ i j b)
    (hw : ∀ (i j : ι) (c : Bi j), ψ i j ((1 : Bi i) ⊗ₜ[A] c) = algebraMap (Bi j) (D i j) c)
    (u₁ : ∀ i j k, Bi i →+* D₃ i j k) (ψ₃ : ∀ i j k, Bi i ⊗[A] D j k ≃+* D₃ i j k)
    (hu : ∀ (i j k : ι) (b : Bi i), ψ₃ i j k (b ⊗ₜ[A] (1 : D j k)) = u₁ i j k b)
    (hw₃ : ∀ (i j k : ι) (d : D j k),
      ψ₃ i j k ((1 : Bi i) ⊗ₜ[A] d) = algebraMap (D j k) (D₃ i j k) d)
    (w₁₂ : ∀ i j k, D i j →+* D₃ i j k) (w₁₃ : ∀ i j k, D i k →+* D₃ i j k)
    (wδ : ∀ i, D i i →+* Bi i)
    (hwδ : ∀ (i : ι) (b : Bi i), wδ i (v₁ i i b) = b)
    (h₁₂ : ∀ (i j k : ι) (b : Bi i), w₁₂ i j k (v₁ i j b) = u₁ i j k b)
    (h₁₃ : ∀ (i j k : ι) (b : Bi i), w₁₃ i j k (v₁ i k b) = u₁ i j k b)
    (hsmq₁ : ∀ (i j : ι) (b : Bi i) (n : N.val.obj (op (Y i))),
      N.val.restrictₛₗ (pr₁ i j).op (b • n) = v₁ i j b • N.val.restrictₛₗ (pr₁ i j).op n)
    (hsmδ : ∀ (i : ι) (d : D i i) (w : N.val.obj (op (Pb i i))),
      N.val.restrictₛₗ (δ i).op (d • w) = wδ i d • N.val.restrictₛₗ (δ i).op w)
    (hsm₁₂ : ∀ (i j k : ι) (d : D i j) (w : N.val.obj (op (Pb i j))),
      N.val.restrictₛₗ (t₁₂ i j k).op (d • w) =
        w₁₂ i j k d • N.val.restrictₛₗ (t₁₂ i j k).op w)
    (hsm₁₃ : ∀ (i j k : ι) (d : D i k) (w : N.val.obj (op (Pb i k))),
      N.val.restrictₛₗ (t₁₃ i j k).op (d • w) =
        w₁₃ i j k d • N.val.restrictₛₗ (t₁₃ i j k).op w)
    (ρ₂ : ∀ i j, N.val.obj (op (Y j)) →ₗ[Bi j] N.val.obj (op (Pb i j)))
    (hρ₂ : ∀ (i j : ι) (n : N.val.obj (op (Y j))),
      ρ₂ i j n = N.val.restrictₛₗ (pr₂ i j).op n)
    (hbij₂ : ∀ i j, Function.Bijective ((ρ₂ i j).liftBaseChange (D i j)))
    (ρ₃ : ∀ i j k, N.val.obj (op (Pb j k)) →ₗ[D j k] N.val.obj (op (Pb₃ i j k)))
    (hρ₃ : ∀ (i j k : ι) (w : N.val.obj (op (Pb j k))),
      ρ₃ i j k w = N.val.restrictₛₗ (t₂₃ i j k).op w)
    (hbij₃ : ∀ i j k, Function.Bijective ((ρ₃ i j k).liftBaseChange (D₃ i j k)))
    (ρ : N.val.obj (op T) →ₗ[A] ∀ i, N.val.obj (op (Y i)))
    (hρ : ∀ (n : N.val.obj (op T)) (i : ι), ρ n i = N.val.restrictₛₗ (g i).op n)
    (ψc : ∀ i, Bi i →+* R.obj.obj (op (Y i)))
    (hψc : ∀ (i : ι) (b : Bi i) (n : N.val.obj (op (Y i))), b • n = ψc i b • n) (i : ι) :
    N.sectionSpan (g i) = ⊤ := by
  obtain ⟨e, e₃, he, he₃, he₃tmul⟩ := Module.Descent.exists_cancelBaseChange_pi_pair A Bi D D₃
    v₁ ψ hv hw u₁ ψ₃ hu hw₃ ρ₂ hbij₂ ρ₃ hbij₃
  refine sectionSpan_eq_top_of_family_baseChange N g pr₁ pr₂ δ t₁₂ t₁₃ t₂₃ hδ₁ hδ₂ hc₁ hc₂ hc₃
    hpb hcov A Bi D D₃ v₁ u₁ w₁₂ w₁₃ wδ hwδ h₁₂ h₁₃ hsmq₁ hsmδ hsm₁₂ hsm₁₃ e
    (fun s uu a b => by rw [he, hρ₂]) e₃ he₃
    (fun s y a b c => by rw [he₃tmul, hρ₃]) ρ hρ ψc hψc i

end SheafOfModules

end
