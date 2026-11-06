module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CechAmitsur
public import StacksFrontier.RingTheory.Descent.EqualizerDescent

/-!
# The descent datum carried by the sections over a covering object

Effectivity of flat descent takes as input a `Module.Descent.Datum`: a coaction which is counital
and coassociative.  A consumer arriving at one from a covering morphism `h : W ⟶ U` of a site does
not hold a coaction; what it holds is the restriction maps to a double self-product `V` of `W` over
`U`, a comparison identifying the sections over `V` with a base change of the sections over `W`,
and the same comparison one degree up on a triple self-product `V₃`.  This file turns that into a
descent datum, and then into the base-change comparison at `W` which Stacks 03DX asserts.

Two of the three fields of a descent datum are produced from restriction maps alone: counitality
from the diagonal `W ⟶ V`, which is a section of both projections, and coassociativity from the
equality `t₁₂ ≫ q₁ = t₁₃ ≫ q₁` of two of the projections of the triple self-product onto the
covering object.  Neither computes with tensor products.  The coaction itself is the one piece of
data: the comparison on the double overlap, read backwards.

The comparison and its degree-one companion are in turn determined by the base-change comparisons
over the two overlaps.  A comparison which carries `b ⊗ₜ n` to `v₁ b • (restriction of n along the
second projection)`, where `v₁` is the ring map of the first projection, is automatically
semilinear for the action of the coefficient ring of the covering object and carries `1 ⊗ₜ n` to a
restriction, so every remaining hypothesis of the datum becomes a composition of restriction maps.
What is left assumed is the three commutations of the triple self-product, the two factorisations
of the identity through the diagonal, the three identities between the ring maps, and the
semilinearity of restriction along each arrow.

The identification then runs through the descended module: it is the locus where the two
restrictions to `V` agree, which is the kernel of the degree-zero Čech differential, and the sheaf
axiom for the one-element covering `{h}` identifies that kernel with the image of restriction from
`U`.  Composing the two memberships is exactly the hypothesis `hmem` of
`Module.Descent.Datum.isBaseChange_of_mem_descended_iff`, so the conclusion is that the sections
over `W` are the base change of the sections over `U`.

## Main results

* `CategoryTheory.IsPullback.exists_diagonal`: the diagonal of a self-product, which is a section
  of both projections.
* `Module.Descent.mem_descended_iff_of_injective`: the descended module is the locus where two
  maps agree, for an injective comparison which is not assumed linear.
* `Module.Descent.exists_datum_of_comparison`: **a descent datum from a comparison on the double
  overlap, a retraction of it, and an injective comparison one degree up**, with the coaction
  characterised by the comparison, so that a later statement about the same coaction can be made.
* `Module.Descent.exists_baseChangeEquiv_of_comparison` and
  `Module.Descent.bijective_liftBaseChange_of_comparison`: **a map whose values are exactly the
  locus where the two comparisons agree exhibits the module as a base change**, in the two shapes
  a consumer of the base-change comparison uses.
* `Module.Descent.span_range_eq_top_of_comparison`: the same hypotheses with one inclusion give
  the weaker statement that the values of the map span, which is the span condition.
* `PresheafOfModules.exists_datum_of_restriction`: **the descent datum carried by the sections of
  a presheaf of modules over a covering object**, whose descended module is the kernel of the
  degree-zero Čech differential.  The counit and cocycle axioms are discharged from the diagonal
  and from one commutation of the triple self-product.
* `PresheafOfModules.exists_datum_of_baseChange`: **the same from the values of the two comparisons
  on pure tensors**, where the only hypotheses left are the semilinearity of restriction along the
  five arrows, the three identities between the induced ring maps, and the commutations of the
  triple self-product and of the diagonal.
* `PresheafOfModules.exists_baseChangeEquiv_of_cechDiff₀`: **the sections over the covering object
  are the base change of the sections over the base**, from such a datum and the sheaf axiom for
  the one-element covering.

## Implementation notes

The hypotheses about the two comparisons are stated in the implication form
`N.restrictₛₗ q₁.op n = e y → …` rather than with `e.symm`, because that is the form in which a
consumer proves them: it knows what restriction along a projection does to a pure tensor of the
comparison, not what the inverse comparison does to a section.

The comparisons are additive maps and the retraction is a bare function: none of the linearity of
`Module.Descent.mem_descended_iff_of_comparison`,
`Module.Descent.counit_coaction_of_retraction` or `Module.Descent.coassoc_of_comparison` is used
in their proofs, and dropping it is what lets a consumer pass the restriction maps of a presheaf
of modules directly.  Those are semilinear along five different ring maps, so there is no single
ring over which they could be read as linear maps, and the module structures over the ring of the
base which reading them as linear maps at all would need are not instances on the sections of a
presheaf of modules.  Only the coaction has to be linear, and `Module.Descent.Datum` asks for
that; it is where `hesm` is used.

`Module.Descent.mem_descended_iff_of_injective` is `Module.Descent.mem_descended_iff_of_comparison`
with the linearity of the comparison and of the two maps dropped, which is a different statement
rather than a duplicate: the comparison of a module of sections over an overlap is semilinear and
not linear, so the linear form does not apply to it.

`Module.Flat` is used only where effectivity of descent is; the datum itself needs no flatness,
and no object is assumed affine or quasi-compact anywhere in the file.

**One covering morphism or a covering family.**  The engine
`Module.Descent.exists_datum_of_comparison` is stated for arbitrary `N₂` and `N₃`, with no
presheaf and no overlap among its data, and that is deliberate: a covering family `{Yᵢ ⟶ U}` is
handled by taking `B` to be the product `∀ i, Bᵢ` of the coefficient rings, `N` the product of the
sections over the members, `N₂` the product of the sections over the fibre products of pairs and
`N₃` the product of the sections over the fibre products of triples, exactly as
`PresheafOfModules.exists_amitsurDiff₀_data` handles the sheaf condition one degree down.  No
coproduct inside the site is formed, which is what makes this route available at all: a disjoint
union of members carries no morphism to the object covered.  The statements in the
`PresheafOfModules` namespace below are the one-element specialisation, where `N₂` and `N₃` are
the sections over a double and a triple self-product of a single covering morphism; they are the
form in which the triple self-product of
`AlgebraicGeometry.FibredSite.exists_affine_triple_self_product` is consumed, and they do not
restrict the engine.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe y z v u

namespace CategoryTheory.IsPullback

/-- **The diagonal of a self-product.**  A fibre product square of a morphism with itself has a
section of both projections, namely the morphism the universal property produces from the identity
and the identity. -/
theorem exists_diagonal {C : Type u} [Category.{v} C] {U W V : C} {h : W ⟶ U} {q₁ q₂ : V ⟶ W}
    (hV : IsPullback q₁ q₂ h h) : ∃ δ : W ⟶ V, δ ≫ q₁ = 𝟙 W ∧ δ ≫ q₂ = 𝟙 W :=
  ⟨hV.lift (𝟙 W) (𝟙 W) rfl, hV.lift_fst _ _ _, hV.lift_snd _ _ _⟩

end CategoryTheory.IsPullback

namespace Module.Descent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- **The descended module is the locus where two maps out of `N` agree**, for an injective
comparison which identifies them with the coaction and with `n ↦ 1 ⊗ₜ n`.

This is `Module.Descent.mem_descended_iff_of_comparison` with the linearity of the comparison and
of the two maps dropped, none of it being used: the comparison identifying the sections of a
presheaf of modules over a double overlap with a base change is semilinear along the ring map of a
projection, not linear over the ring of the base, so the linear form does not apply to it. -/
theorem mem_descended_iff_of_injective {N₂ : Type*} (d : Datum A B N)
    (e : B ⊗[A] N → N₂) (he : Function.Injective e) (p q : N → N₂)
    (hp : ∀ n, p n = e (d.coaction n)) (hq : ∀ n, q n = e ((1 : B) ⊗ₜ[A] n)) {n : N} :
    n ∈ d.descended ↔ p n = q n := by
  rw [Datum.mem_descended_iff, hp, hq]
  exact ⟨fun h => congrArg e h, fun h => he h⟩

/-- **A descent datum from a comparison on the double overlap, a retraction of it, and an
injective comparison on the triple overlap.**

Let `e` identify `B ⊗[A] N` additively with a group `N₂`, let `p : N →+ N₂` be a second map which
`hesm` says is compatible with the action of `B` through `e`, let `r` be a retraction of `p`
carrying `e` to the counit, and let `e₃` inject `B ⊗[A] (B ⊗[A] N)` into a group `N₃` in such a way
that two maps `u`, `v` out of `N₂` describe its two values of interest.  If `u` and `v` agree on
the values of `p`, then `N` carries a descent datum whose coaction is `p` read backwards through
`e`.

For the sections of a presheaf of modules on a covering morphism `h : W ⟶ U`, `N₂` and `N₃` are
the sections over a double and a triple self-product of `W` over `U`, `p` is restriction along the
first projection, `r` is restriction along the diagonal, and `u`, `v` are restrictions along two
of the three projections of the triple self-product; the last hypothesis is then functoriality of
restriction along one commutation.  See
`PresheafOfModules.exists_datum_of_restriction`. -/
theorem exists_datum_of_comparison {N₂ N₃ : Type*} [AddCommGroup N₂] [AddCommGroup N₃]
    (e : B ⊗[A] N ≃+ N₂) (p : N →+ N₂)
    (hesm : ∀ (b : B) (n : N) (y : B ⊗[A] N), p n = e y → p (b • n) = e (b • y))
    (r : N₂ → N) (hrp : ∀ n, r (p n) = n)
    (hre : ∀ x, r (e x) = counit A B N x)
    (e₃ : B ⊗[A] (B ⊗[A] N) →+ N₃) (he₃ : Function.Injective e₃)
    (u v : N₂ →+ N₃)
    (hu : ∀ (b : B) (n : N) (y : B ⊗[A] N), p n = e y →
      e₃ (b ⊗ₜ[A] y) = u (e (b ⊗ₜ[A] n)))
    (hv : ∀ (b : B) (n : N), e₃ (b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] n)) = v (e (b ⊗ₜ[A] n)))
    (huv : ∀ n, u (p n) = v (p n)) :
    ∃ d : Datum A B N, ∀ n, e (d.coaction n) = p n := by
  let c : N →ₗ[B] B ⊗[A] N :=
    { toFun := fun n => e.symm (p n)
      map_add' := fun n n' => by rw [map_add, map_add]
      map_smul' := fun b n => by
        refine e.injective ?_
        rw [e.apply_symm_apply]
        exact hesm b n (e.symm (p n)) (e.apply_symm_apply (p n)).symm }
  have hc : ∀ n, p n = e (c n) := fun n => (e.apply_symm_apply (p n)).symm
  have hl : ∀ (L : N →ₗ[A] B ⊗[A] N) (w : N₂ →+ N₃),
      (∀ (b : B) (n : N), e₃ (b ⊗ₜ[A] L n) = w (e (b ⊗ₜ[A] n))) →
      ∀ x : B ⊗[A] N, e₃ (AlgebraTensorModule.lTensor B B L x) = w (e x) := fun L w hL x => by
    induction x with
    | tmul b n => rw [AlgebraTensorModule.lTensor_tmul]; exact hL b n
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have hlu := hl (c.restrictScalars A) u fun b n => hu b n (c n) (hc n)
  have hlv := hl (TensorProduct.mk A B N 1) v hv
  exact ⟨{ coaction := c
           counit_coaction := fun n => by rw [← hre, ← hc, hrp]
           coassoc := fun n => he₃ (by rw [hlu, hlv, ← hc, huv]) },
    fun n => (hc n).symm⟩

section Flat

variable {M N₂ : Type*} [AddCommGroup M] [Module A M] [Module.Flat A B]

/-- **A map whose values are exactly the locus where the two comparisons agree exhibits the module
as a base change.**  Let `d` be a descent datum on `N`, let `e` inject `B ⊗[A] N` into `N₂` and
identify the coaction with `p` and `n ↦ 1 ⊗ₜ n` with `q`, and let `ρ : M →ₗ[A] N` be injective with
image exactly the locus where `p` and `q` agree.  Then `ρ` exhibits `N` as the base change of `M`
along a flat ring map. -/
theorem exists_baseChangeEquiv_of_comparison (d : Datum A B N)
    (e : B ⊗[A] N → N₂) (he : Function.Injective e) (p q : N → N₂)
    (hp : ∀ n, p n = e (d.coaction n)) (hq : ∀ n, q n = e ((1 : B) ⊗ₜ[A] n))
    (ρ : M →ₗ[A] N) (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, p n = q n ↔ n ∈ LinearMap.range ρ) :
    ∃ eqv : B ⊗[A] M ≃ₗ[B] N, ∀ m : M, eqv ((1 : B) ⊗ₜ[A] m) = ρ m :=
  d.exists_baseChangeEquiv_of_mem_descended_iff ρ hinj
    fun n => (mem_descended_iff_of_injective A B d e he p q hp hq).trans (hmem n)

/-- `Module.Descent.exists_baseChangeEquiv_of_comparison` as bijectivity of the base change of
`ρ`, which is the shape in which the base-change comparison of a module of sections is stated. -/
theorem bijective_liftBaseChange_of_comparison (d : Datum A B N)
    (e : B ⊗[A] N → N₂) (he : Function.Injective e) (p q : N → N₂)
    (hp : ∀ n, p n = e (d.coaction n)) (hq : ∀ n, q n = e ((1 : B) ⊗ₜ[A] n))
    (ρ : M →ₗ[A] N) (hinj : Function.Injective ρ)
    (hmem : ∀ n : N, p n = q n ↔ n ∈ LinearMap.range ρ) :
    Function.Bijective (ρ.liftBaseChange B) :=
  d.bijective_liftBaseChange_of_mem_descended_iff ρ hinj
    fun n => (mem_descended_iff_of_injective A B d e he p q hp hq).trans (hmem n)

/-- **The values of the map span**, under the hypotheses of
`Module.Descent.exists_baseChangeEquiv_of_comparison` weakened to one inclusion.  Only that every
element of the locus where the two comparisons agree is a value of `ρ` is used, and neither the
injectivity of `ρ` nor the converse inclusion. -/
theorem span_range_eq_top_of_comparison (d : Datum A B N)
    (e : B ⊗[A] N → N₂) (he : Function.Injective e) (p q : N → N₂)
    (hp : ∀ n, p n = e (d.coaction n)) (hq : ∀ n, q n = e ((1 : B) ⊗ₜ[A] n))
    (ρ : M →ₗ[A] N) (hmem : ∀ n : N, p n = q n → n ∈ LinearMap.range ρ) :
    Submodule.span B (Set.range ρ) = ⊤ :=
  span_range_eq_top_of_descended_le A B d ρ fun n hn =>
    hmem n ((mem_descended_iff_of_injective A B d e he p q hp hq).1 hn)

end Flat

end Module.Descent

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{z}}

/-- **The descent datum carried by the sections of a presheaf of modules over a covering
object.**  Let `q₁, q₂ : V ⟶ W` be the two projections of a double self-product of `W` over the
object covered, let `δ : W ⟶ V` be the diagonal and let `t₁₂, t₁₃ : V₃ ⟶ V` be two of the three
projections of a triple self-product onto the double one.  Let the sections over `W` be a module
over a commutative ring `B` which is an algebra over a commutative ring `A`, let `e` identify
`B ⊗[A] N(W)` additively with the sections over `V` so that `1 ⊗ₜ n` is the restriction along
`q₂`, and let `e₃` inject `B ⊗[A] (B ⊗[A] N(W))` into the sections over `V₃`.  Then the sections
over `W` carry a descent datum whose descended module is the kernel of the degree-zero Čech
differential.

The counit axiom is `δ ≫ q₁ = 𝟙 W`, the diagonal being a section of the first projection, and the
cocycle axiom is `t₁₂ ≫ q₁ = t₁₃ ≫ q₁`, two of the projections of the triple self-product onto the
covering object agreeing; both enter only through functoriality of restriction
(`PresheafOfModules.restrictₛₗ_restrictₛₗ_op`).  What is genuinely assumed about the sections is
the pair of comparisons and their values on pure tensors, which over an affine object is
quasi-coherence; `PresheafOfModules.exists_datum_of_baseChange` discharges the remaining four
hypotheses from those values.

The conclusion is stated for `PresheafOfModules.cechDiff₀` rather than as the equality of the two
restrictions because that is the form the sheaf axiom for a one-element covering comes in. -/
theorem exists_datum_of_restriction {N : PresheafOfModules.{y} R} {W V V₃ : C}
    (q₁ q₂ : V ⟶ W) (δ : W ⟶ V) (t₁₂ t₁₃ : V₃ ⟶ V)
    (hδ : δ ≫ q₁ = 𝟙 W) (ht : t₁₂ ≫ q₁ = t₁₃ ≫ q₁)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module A (N.obj (op W))] [Module B (N.obj (op W))] [IsScalarTower A B (N.obj (op W))]
    (e : B ⊗[A] N.obj (op W) ≃+ N.obj (op V))
    (he₁ : ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.restrictₛₗ q₂.op n)
    (hesm : ∀ (b : B) (n : N.obj (op W)) (y : B ⊗[A] N.obj (op W)),
      N.restrictₛₗ q₁.op n = e y → N.restrictₛₗ q₁.op (b • n) = e (b • y))
    (hre : ∀ x, N.restrictₛₗ δ.op (e x) = Module.Descent.counit A B (N.obj (op W)) x)
    (e₃ : B ⊗[A] (B ⊗[A] N.obj (op W)) →+ N.obj (op V₃)) (he₃ : Function.Injective e₃)
    (hu₃ : ∀ (b : B) (n : N.obj (op W)) (y : B ⊗[A] N.obj (op W)),
      N.restrictₛₗ q₁.op n = e y →
        e₃ (b ⊗ₜ[A] y) = N.restrictₛₗ t₁₂.op (e (b ⊗ₜ[A] n)))
    (hv₃ : ∀ (b : B) (n : N.obj (op W)),
      e₃ (b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] n)) = N.restrictₛₗ t₁₃.op (e (b ⊗ₜ[A] n))) :
    ∃ d : Module.Descent.Datum A B (N.obj (op W)),
      ∀ n, n ∈ d.descended ↔ N.cechDiff₀ q₁ q₂ n = 0 := by
  have hrp : ∀ n, N.restrictₛₗ δ.op (N.restrictₛₗ q₁.op n) = n := fun n => by
    rw [N.restrictₛₗ_restrictₛₗ_op, hδ]
    simp
  have huv : ∀ n, N.restrictₛₗ t₁₂.op (N.restrictₛₗ q₁.op n) =
      N.restrictₛₗ t₁₃.op (N.restrictₛₗ q₁.op n) := fun n => by
    rw [N.restrictₛₗ_restrictₛₗ_op, N.restrictₛₗ_restrictₛₗ_op, ht]
  obtain ⟨d, hd⟩ := Module.Descent.exists_datum_of_comparison A B e
    (N.restrictₛₗ q₁.op).toAddMonoidHom hesm (fun z => N.restrictₛₗ δ.op z) hrp hre e₃ he₃
    (N.restrictₛₗ t₁₂.op).toAddMonoidHom (N.restrictₛₗ t₁₃.op).toAddMonoidHom hu₃ hv₃ huv
  refine ⟨d, fun n => ?_⟩
  rw [Module.Descent.mem_descended_iff_of_injective A B d e e.injective
    (fun n => N.restrictₛₗ q₁.op n) (fun n => e ((1 : B) ⊗ₜ[A] n)) (fun n => (hd n).symm)
    (fun _ => rfl), cechDiff₀_apply, sub_eq_zero, he₁ n]

/-- **The descent datum carried by the sections over a covering object, from the values of the two
base-change comparisons on pure tensors.**

Let `v₁` be the ring map of the first projection of the double self-product, `u₁` that of the
first projection of the triple self-product onto the covering object, `w₁₂` and `w₁₃` those of two
of the three projections of the triple self-product onto the double one, and `wδ` that of the
diagonal.  Suppose the comparison on the double overlap carries `b ⊗ₜ n` to
`v₁ b • (restriction of n along q₂)` and the one on the triple overlap carries `b ⊗ₜ y` to
`u₁ b • (restriction of e y along t₂₃)`.  Then the four remaining hypotheses of
`PresheafOfModules.exists_datum_of_restriction` are theorems, and the sections over `W` carry a
descent datum whose descended module is the kernel of the degree-zero Čech differential.

Every hypothesis is either a commutation of the triple self-product
(`AlgebraicGeometry.FibredSite.exists_affine_triple_self_product` returns the three), a
factorisation of the identity through the diagonal, an identity between the induced ring maps, or
semilinearity of restriction along one arrow.  So no tensor calculus is left in the passage from
quasi-coherence on the slice at the covering object to the descent datum. -/
theorem exists_datum_of_baseChange {N : PresheafOfModules.{y} R} {W V V₃ : C}
    (q₁ q₂ : V ⟶ W) (δ : W ⟶ V) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V)
    (hδ₁ : δ ≫ q₁ = 𝟙 W) (hδ₂ : δ ≫ q₂ = 𝟙 W)
    (hc₁ : t₁₂ ≫ q₁ = t₁₃ ≫ q₁) (hc₂ : t₁₂ ≫ q₂ = t₂₃ ≫ q₁) (hc₃ : t₁₃ ≫ q₂ = t₂₃ ≫ q₂)
    (A B D₂ D₃ : Type*) [CommRing A] [CommRing B] [CommRing D₂] [CommRing D₃] [Algebra A B]
    [Module A (N.obj (op W))] [Module B (N.obj (op W))] [IsScalarTower A B (N.obj (op W))]
    [Module D₂ (N.obj (op V))] [Module D₃ (N.obj (op V₃))]
    (v₁ : B →+* D₂) (u₁ : B →+* D₃) (w₁₂ w₁₃ : D₂ →+* D₃) (wδ : D₂ →+* B)
    (hwδ : ∀ b, wδ (v₁ b) = b) (h₁₂ : ∀ b, w₁₂ (v₁ b) = u₁ b)
    (h₁₃ : ∀ b, w₁₃ (v₁ b) = u₁ b)
    (hsmq₁ : ∀ (b : B) (n : N.obj (op W)),
      N.restrictₛₗ q₁.op (b • n) = v₁ b • N.restrictₛₗ q₁.op n)
    (hsmδ : ∀ (d : D₂) (z : N.obj (op V)),
      N.restrictₛₗ δ.op (d • z) = wδ d • N.restrictₛₗ δ.op z)
    (hsm₁₂ : ∀ (d : D₂) (z : N.obj (op V)),
      N.restrictₛₗ t₁₂.op (d • z) = w₁₂ d • N.restrictₛₗ t₁₂.op z)
    (hsm₁₃ : ∀ (d : D₂) (z : N.obj (op V)),
      N.restrictₛₗ t₁₃.op (d • z) = w₁₃ d • N.restrictₛₗ t₁₃.op z)
    (e : B ⊗[A] N.obj (op W) ≃+ N.obj (op V))
    (he : ∀ (b : B) (n : N.obj (op W)),
      e (b ⊗ₜ[A] n) = v₁ b • N.restrictₛₗ q₂.op n)
    (e₃ : B ⊗[A] (B ⊗[A] N.obj (op W)) →+ N.obj (op V₃)) (he₃ : Function.Injective e₃)
    (he₃tmul : ∀ (b : B) (y : B ⊗[A] N.obj (op W)),
      e₃ (b ⊗ₜ[A] y) = u₁ b • N.restrictₛₗ t₂₃.op (e y)) :
    ∃ d : Module.Descent.Datum A B (N.obj (op W)),
      ∀ n, n ∈ d.descended ↔ N.cechDiff₀ q₁ q₂ n = 0 := by
  have he₁ : ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.restrictₛₗ q₂.op n := fun n => by
    rw [he, map_one, one_smul]
  have hes : ∀ (b : B) (y : B ⊗[A] N.obj (op W)), e (b • y) = v₁ b • e y := fun b y => by
    induction y with
    | tmul b' n => rw [TensorProduct.smul_tmul', smul_eq_mul, he, he, map_mul, mul_smul]
    | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]
  refine exists_datum_of_restriction q₁ q₂ δ t₁₂ t₁₃ hδ₁ hc₁ A B e he₁
    (fun b n y hny => by rw [hsmq₁, hny, hes]) (fun x => ?_) e₃ he₃
    (fun b n y hny => by
      rw [he₃tmul, ← hny, N.restrictₛₗ_restrictₛₗ_op, he, hsm₁₂, h₁₂,
        N.restrictₛₗ_restrictₛₗ_op, hc₂])
    fun b n => by
      rw [he₃tmul, he₁, N.restrictₛₗ_restrictₛₗ_op, he, hsm₁₃, h₁₃,
        N.restrictₛₗ_restrictₛₗ_op, hc₃]
  induction x with
  | tmul b n =>
    rw [he, hsmδ, hwδ, N.restrictₛₗ_restrictₛₗ_op, hδ₂]
    simp
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add]

/-- **The sections over the covering object are the base change of the sections over the base.**
Let `d` be a descent datum on the sections over `W` whose descended module is the kernel of the
degree-zero Čech differential of a double self-product of `W` over `U`, as
`PresheafOfModules.exists_datum_of_baseChange` produces, and let restriction along `h` be
injective with image exactly that kernel.  Then restriction along `h` exhibits the sections over
`W` as the base change of the sections over `U` along a flat ring map.

The two hypotheses beyond the datum are exactly the sheaf axiom for the one-element covering
`{h}`, in its two halves: `hinj` is separatedness and `hsheaf` is the existence of the
amalgamation.  This is the base-change comparison Stacks 03DX asserts at an object covered by an
object on whose slice the module is globally presented, that presentation being what produces the
comparison on the double overlap. -/
theorem exists_baseChangeEquiv_of_cechDiff₀ {N : PresheafOfModules.{y} R} {U W V : C}
    (h : W ⟶ U) (q₁ q₂ : V ⟶ W) (hq : q₁ ≫ h = q₂ ≫ h)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    [Module A (N.obj (op U))]
    [Module A (N.obj (op W))] [Module B (N.obj (op W))] [IsScalarTower A B (N.obj (op W))]
    (d : Module.Descent.Datum A B (N.obj (op W)))
    (hd : ∀ n, n ∈ d.descended ↔ N.cechDiff₀ q₁ q₂ n = 0)
    (ρ : N.obj (op U) →ₗ[A] N.obj (op W)) (hρ : ∀ n, ρ n = N.restrictₛₗ h.op n)
    (hinj : Function.Injective ρ)
    (hsheaf : ∀ z : N.obj (op W), N.cechDiff₀ q₁ q₂ z = 0 → ∃ n, ρ n = z) :
    ∃ eqv : B ⊗[A] N.obj (op U) ≃ₗ[B] N.obj (op W),
      ∀ n, eqv ((1 : B) ⊗ₜ[A] n) = N.restrictₛₗ h.op n := by
  obtain ⟨eqv, heqv⟩ := d.exists_baseChangeEquiv_of_mem_descended_iff ρ hinj fun n =>
    (hd n).trans ⟨hsheaf n, by
      rintro ⟨m, rfl⟩
      rw [hρ]
      exact N.cechDiff₀_restrictₛₗ h q₁ q₂ hq m⟩
  exact ⟨eqv, fun n => (heqv n).trans (hρ n)⟩

end PresheafOfModules

end
