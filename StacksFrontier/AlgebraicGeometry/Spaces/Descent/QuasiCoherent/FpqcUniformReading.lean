module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DescentIsoGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcLegRefinement

/-!
# The isomorphism glued from the readings of a descent datum, and its uniform reading

Let `(w i : W i ⟶ R)` be an fpqc covering, let `ρ : R ⟶ X`, let `D` be a descent datum for
quasi-coherent modules relative to `(w i ≫ ρ)` whose base change to `R` is the canonical descent
datum of an `𝒪_R`-module `N` — that is the hypothesis `hcan` — and let `A` be an algebraic space
carrying two morphisms `c₁, c₂ : A ⟶ R` with equal composites to `X`.

**This file produces an isomorphism `Φ : c₁^*N ≅ c₂^*N` whose reading on every test space over
`A` which maps to members of the covering is the reading of `D`**, and that reading is uniform:
it does not depend on which members, nor on which morphisms to them, the test space is read
through.

Two coverings enter.  `…exists_isFpqcCovering_legPair` covers `A` by spaces mapping to members
of `(w i)` over *both* `c₁` and `c₂`; on such a member the reading of `D` is defined, the
readings agree by `…readN_legs`, and `…exists_mapIso_eq_unreadIso` glues them.  For the uniform
reading, `…exists_isFpqcCovering_leg` covers an arbitrary test space over `A` by spaces mapping
to the members of the first covering, and the faithfulness half of Stacks 04W8 identifies the
two readings there.

At `A = R ×_X R` and the two projections this is the pairwise isomorphism of the descent datum
of `N` relative to the one-member family `{ρ}`, with the uniform reading supplying both its
cocycle condition and its comparison with `D`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.mapIso_eq_unreadIso_comp`: the reading of an
  isomorphism propagates to a test space over the one it is known at.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readingsAgree_readN`: the readings of `D` at the
  members of a two-leg covering agree, which is the hypothesis the gluing consumes.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_mapIso_eq_unreadIso_readN`: **the
  isomorphism `Φ`, with its uniform reading.**

## Implementation notes

The per-member step of the uniform reading is a declaration of its own,
`…mapIso_eq_unreadIso_readN_member`, with the member and the morphisms into it as variables: the
two coverings are obtained in the existence statement and the member statement is instantiated
at each member, so that no covering is ever carried inside a proof that also performs the
cancellations.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Propagate

variable {R : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS R.1 R.2)
  {A : AlgebraicSpaces B S hS} (c₁ c₂ : A ⟶ R)

/-- **The reading of an isomorphism of the two inverse images of `N` propagates to a test space
over the one its reading is known at.**  The reading on the second space is the reading of the
first one there. -/
theorem mapIso_eq_unreadIso_comp
    (Φ : (modulePullback B S hS c₁).obj N ≅ (modulePullback B S hS c₂).obj N)
    {T : AlgebraicSpaces B S hS} (p : T ⟶ A) (xx yy : T ⟶ R) (hpx : p ≫ c₁ = xx)
    (hpy : p ≫ c₂ = yy)
    (GG : (modulePullback B S hS xx).obj N ≅ (modulePullback B S hS yy).obj N)
    (h : (modulePullback B S hS p).mapIso Φ =
      unreadIso B S hS N c₁ c₂ p xx yy hpx hpy GG)
    {P : AlgebraicSpaces B S hS} (r : P ⟶ T) (e : P ⟶ A) (he : r ≫ p = e)
    (x' y' : P ⟶ R) (hx' : e ≫ c₁ = x') (hy' : e ≫ c₂ = y') (hrx : r ≫ xx = x')
    (hry : r ≫ yy = y') :
    (modulePullback B S hS e).mapIso Φ =
      unreadIso B S hS N c₁ c₂ e x' y' hx' hy'
        (pullbackComparison B S hS r xx x' hrx N ≪≫
          (modulePullback B S hS r).mapIso GG ≪≫
          (pullbackComparison B S hS r yy y' hry N).symm) := by
  subst he
  have h1 := modulePullback_mapIso_mapIso B S hS r p (r ≫ p) rfl Φ
  have h2 := mapIso_unreadIso B S hS N c₁ c₂ p xx yy hpx hpy GG r (r ≫ p) rfl x' y' hx' hy'
    hrx hry
  rw [h] at h1
  rw [h1] at h2
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]
    using h2

end Propagate

section Uniform

variable {I : Type v} {X R : AlgebraicSpaces B S hS} (W : I → AlgebraicSpaces B S hS)
  (w : ∀ i, W i ⟶ R) (ρ : R ⟶ X) (D : DescentDatum B S hS W (fun t => w t ≫ ρ))
  (N : Modules.{u, u} B S hS R.1 R.2)
  (ε : ∀ i, D.F i ≅ (modulePullback B S hS (w i)).obj N)
  (hcan : ∀ i j, (modulePullback B S hS (pairFst B S hS W w i j)).mapIso (ε i) ≪≫
      canonicalComparison (pairFst B S hS W w i j) (pairSnd B S hS W w i j) (w i) (w j)
        (pair_condition B S hS W w i j) N =
    baseChangeTransition B S hS W w ρ D i j ≪≫
      (modulePullback B S hS (pairSnd B S hS W w i j)).mapIso (ε j))

/-- **Two readings of `D`, pulled back to a common test space and read at the same composites to
`R`, agree.**  Both are the reading at the pulled-back legs by `…readN_map`, and those agree by
`…readN_legs`. -/
private theorem comparison_mapIso_readN_eq
    (hcan : ∀ i j, (modulePullback B S hS (pairFst B S hS W w i j)).mapIso (ε i) ≪≫
      canonicalComparison (pairFst B S hS W w i j) (pairSnd B S hS W w i j) (w i) (w j)
        (pair_condition B S hS W w i j) N =
      baseChangeTransition B S hS W w ρ D i j ≪≫
        (modulePullback B S hS (pairSnd B S hS W w i j)).mapIso (ε j))
    {T T' P : AlgebraicSpaces B S hS}
    (i j i' j' : I) (α : T ⟶ W i) (β : T ⟶ W j) (x y : T ⟶ R) (hx : α ≫ w i = x)
    (hy : β ≫ w j = y) (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β)
    (α' : T' ⟶ W i') (β' : T' ⟶ W j') (x₂ y₂ : T' ⟶ R) (hx₂ : α' ≫ w i' = x₂)
    (hy₂ : β' ≫ w j' = y₂) (v' : T' ⟶ pair B S hS W (fun t => w t ≫ ρ) i' j')
    (hv₁' : v' ≫ pairFst B S hS W (fun t => w t ≫ ρ) i' j' = α')
    (hv₂' : v' ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i' j' = β')
    (s : P ⟶ T) (t : P ⟶ T') (x' y' : P ⟶ R) (hsx : s ≫ x = x') (hsy : s ≫ y = y')
    (htx : t ≫ x₂ = x') (hty : t ≫ y₂ = y') :
    pullbackComparison B S hS s x x' hsx N ≪≫
        (modulePullback B S hS s).mapIso (readN B S hS W w ρ D N ε i j α β x y hx hy v hv₁ hv₂) ≪≫
        (pullbackComparison B S hS s y y' hsy N).symm =
      pullbackComparison B S hS t x₂ x' htx N ≪≫
        (modulePullback B S hS t).mapIso
          (readN B S hS W w ρ D N ε i' j' α' β' x₂ y₂ hx₂ hy₂ v' hv₁' hv₂') ≪≫
        (pullbackComparison B S hS t y₂ y' hty N).symm := by
  rw [readN_map B S hS W w ρ D N ε s i j α β x y hx hy v hv₁ hv₂ (s ≫ α) (s ≫ β) rfl rfl x' y'
      hsx hsy (by rw [Category.assoc, hx, hsx]) (by rw [Category.assoc, hy, hsy])
      (by rw [Category.assoc, hv₁]) (by rw [Category.assoc, hv₂]),
    readN_map B S hS W w ρ D N ε t i' j' α' β' x₂ y₂ hx₂ hy₂ v' hv₁' hv₂' (t ≫ α') (t ≫ β') rfl
      rfl x' y' htx hty (by rw [Category.assoc, hx₂, htx]) (by rw [Category.assoc, hy₂, hty])
      (by rw [Category.assoc, hv₁']) (by rw [Category.assoc, hv₂'])]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]
  exact readN_legs B S hS W w ρ D N ε hcan i j i' j' (s ≫ α) (s ≫ β) (t ≫ α') (t ≫ β') x' y'
    (by rw [Category.assoc, hx, hsx]) (by rw [Category.assoc, hy, hsy])
    (by rw [Category.assoc, hx₂, htx]) (by rw [Category.assoc, hy₂, hty])
    (s ≫ v) (by rw [Category.assoc, hv₁]) (by rw [Category.assoc, hv₂])
    (t ≫ v') (by rw [Category.assoc, hv₁']) (by rw [Category.assoc, hv₂'])

include hcan in
/-- **The readings of `D` at the members of a two-leg covering agree on every test space mapping
to two of those members.**  Each reading is the reading of `D` at the legs composed with the
morphism from the test space, by `…readN_map`, and those depend on the legs only through their
composites to `R`, by `…readN_legs`. -/
theorem readingsAgree_readN {K : Type v} (Z : K → AlgebraicSpaces B S hS) (ι κ : K → I)
    (a : ∀ k, Z k ⟶ W (ι k)) (b : ∀ k, Z k ⟶ W (κ k))
    (vk : ∀ k, Z k ⟶ pair B S hS W (fun t => w t ≫ ρ) (ι k) (κ k))
    (hvk₁ : ∀ k, vk k ≫ pairFst B S hS W (fun t => w t ≫ ρ) (ι k) (κ k) = a k)
    (hvk₂ : ∀ k, vk k ≫ pairSnd B S hS W (fun t => w t ≫ ρ) (ι k) (κ k) = b k) :
    ReadingsAgree B S hS N Z (fun k => a k ≫ w (ι k)) (fun k => b k ≫ w (κ k))
      (fun k => readN B S hS W w ρ D N ε (ι k) (κ k) (a k) (b k) (a k ≫ w (ι k))
        (b k ≫ w (κ k)) rfl rfl (vk k) (hvk₁ k) (hvk₂ k)) :=
  readingsAgree_mk B S hS N Z _ _ _ fun _ _ _ _ _ _ _ hx₁ hy₁ hx₂ hy₂ =>
    comparison_mapIso_readN_eq B S hS W w ρ D N ε hcan (hsx := hx₁) (hsy := hy₁) (htx := hx₂)
      (hty := hy₂) ..

variable {A : AlgebraicSpaces B S hS} (c₁ c₂ : A ⟶ R)

include hcan in
/-- **One member of a covering of a test space identifies the reading of the glued isomorphism
there with the reading of `D`.**  The member maps to a member `Zk` of the two-leg covering of
`A`, over the morphism of the test space to `A`; the reading of the glued isomorphism propagates
from `Zk` by `…mapIso_eq_unreadIso_comp`, the reading of `D` propagates by `…readN_map`, and the
two agree by `…readN_legs`. -/
theorem mapIso_eq_unreadIso_readN_member {Zk : AlgebraicSpaces B S hS} (ck : Zk ⟶ A)
    (ik jk : I) (ak : Zk ⟶ W ik) (bk : Zk ⟶ W jk) (hak : ak ≫ w ik = ck ≫ c₁)
    (hbk : bk ≫ w jk = ck ≫ c₂)
    (vki : Zk ⟶ pair B S hS W (fun t => w t ≫ ρ) ik jk)
    (hvki₁ : vki ≫ pairFst B S hS W (fun t => w t ≫ ρ) ik jk = ak)
    (hvki₂ : vki ≫ pairSnd B S hS W (fun t => w t ≫ ρ) ik jk = bk)
    (Φ : (modulePullback B S hS c₁).obj N ≅ (modulePullback B S hS c₂).obj N)
    (hΦ : (modulePullback B S hS ck).mapIso Φ =
      unreadIso B S hS N c₁ c₂ ck (ak ≫ w ik) (bk ≫ w jk) hak.symm hbk.symm
        (readN B S hS W w ρ D N ε ik jk ak bk (ak ≫ w ik) (bk ≫ w jk) rfl rfl vki hvki₁ hvki₂))
    {T : AlgebraicSpaces B S hS} (q : T ⟶ A) (i j : I) (α : T ⟶ W i) (β : T ⟶ W j)
    (xx yy : T ⟶ R) (hqx : q ≫ c₁ = xx) (hqy : q ≫ c₂ = yy) (hax : α ≫ w i = xx)
    (hby : β ≫ w j = yy) (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β)
    {P : AlgebraicSpaces B S hS} (r : P ⟶ T) (rk : P ⟶ Zk) (hr : rk ≫ ck = r ≫ q) :
    (modulePullback B S hS r).mapIso ((modulePullback B S hS q).mapIso Φ) =
      (modulePullback B S hS r).mapIso (unreadIso B S hS N c₁ c₂ q xx yy hqx hqy
        (readN B S hS W w ρ D N ε i j α β xx yy hax hby v hv₁ hv₂)) := by
  refine Iso.cancel_conj
    (pullbackComparison B S hS r q (r ≫ q) rfl ((modulePullback B S hS c₁).obj N))
    (pullbackComparison B S hS r q (r ≫ q) rfl ((modulePullback B S hS c₂).obj N)).symm ?_
  rw [modulePullback_mapIso_mapIso B S hS r q (r ≫ q) rfl Φ,
    mapIso_unreadIso B S hS N c₁ c₂ q xx yy hqx hqy
      (readN B S hS W w ρ D N ε i j α β xx yy hax hby v hv₁ hv₂) r (r ≫ q) rfl
      ((r ≫ q) ≫ c₁) ((r ≫ q) ≫ c₂) rfl rfl
      (by rw [← hqx, ← Category.assoc]) (by rw [← hqy, ← Category.assoc]),
    mapIso_eq_unreadIso_comp B S hS N c₁ c₂ Φ ck (ak ≫ w ik) (bk ≫ w jk) hak.symm hbk.symm _ hΦ
      rk (r ≫ q) hr ((r ≫ q) ≫ c₁) ((r ≫ q) ≫ c₂) rfl rfl
      (by rw [hak, ← Category.assoc, hr]) (by rw [hbk, ← Category.assoc, hr]),
    comparison_mapIso_readN_eq B S hS W w ρ D N ε hcan ik jk i j ak bk (ak ≫ w ik) (bk ≫ w jk)
      rfl rfl vki hvki₁ hvki₂ α β xx yy hax hby v hv₁ hv₂ rk r ((r ≫ q) ≫ c₁) ((r ≫ q) ≫ c₂)
      (by rw [hak, ← Category.assoc, hr]) (by rw [hbk, ← Category.assoc, hr])
      (by rw [← hqx, ← Category.assoc]) (by rw [← hqy, ← Category.assoc])]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]

include hcan in
/-- **The isomorphism of the two inverse images of `N` glued from the readings of `D`, with its
uniform reading**: its reading on every test space over `A` mapping to a member of the covering,
along any two such morphisms, is the reading of `D`.

The two-leg covering of `A` is `…exists_isFpqcCovering_legPair`, the gluing is
`…exists_mapIso_eq_unreadIso`, and the uniform reading is
`…mapIso_eq_unreadIso_readN_member` at the members of the covering of the test space produced by
`…exists_isFpqcCovering_leg`, the two readings being identified there and the faithfulness half
of Stacks 04W8 carrying that back. -/
theorem exists_mapIso_eq_unreadIso_readN (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    (hN : N.IsQuasicoherentOnSite) (hc : c₁ ≫ ρ = c₂ ≫ ρ) :
    ∃ Φ : (modulePullback B S hS c₁).obj N ≅ (modulePullback B S hS c₂).obj N,
      ∀ (T : AlgebraicSpaces B S hS) (q : T ⟶ A) (i j : I) (α : T ⟶ W i) (β : T ⟶ W j)
        (xx yy : T ⟶ R) (hqx : q ≫ c₁ = xx) (hqy : q ≫ c₂ = yy) (hax : α ≫ w i = xx)
        (hby : β ≫ w j = yy) (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
        (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
        (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β),
      (modulePullback B S hS q).mapIso Φ =
        unreadIso B S hS N c₁ c₂ q xx yy hqx hqy
          (readN B S hS W w ρ D N ε i j α β xx yy hax hby v hv₁ hv₂) := by
  classical
  obtain ⟨K', Z', cc', ι', κ', a', b', hcov', ha', hb'⟩ :=
    exists_isFpqcCovering_legPair B S hS W w hw c₁ c₂
  choose vk' hvk₁' hvk₂' using fun k =>
    exists_pairLeg B S hS W (fun t => w t ≫ ρ) (ι' k) (κ' k) (a' k) (b' k)
      (by rw [← Category.assoc, ← Category.assoc, ha' k, hb' k, Category.assoc,
        Category.assoc, hc])
  obtain ⟨Φ, hΦ⟩ := exists_mapIso_eq_unreadIso B S hS N c₁ c₂ Z' cc'
    (fun k => a' k ≫ w (ι' k)) (fun k => b' k ≫ w (κ' k))
    (fun k => (ha' k).symm) (fun k => (hb' k).symm) _ hN hcov'
    (readingsAgree_readN B S hS W w ρ D N ε hcan Z' ι' κ' a' b' vk' hvk₁' hvk₂')
  refine ⟨Φ, fun T q i j α β xx yy hqx hqy hax hby v hv₁ hv₂ => ?_⟩
  obtain ⟨Z'', c'', a'', hcov'', ha''⟩ := exists_isFpqcCovering_leg B S hS Z' cc' hcov' q
  refine Iso.ext (modulePullback_map_injective_of_isFpqcCovering B S hS
    (reprFpqcHomInjective B S hS) Z'' c'' hcov'' _ _ fun n => ?_)
  simpa only [Functor.mapIso_hom] using congrArg Iso.hom
    (mapIso_eq_unreadIso_readN_member B S hS W w ρ D N ε hcan c₁ c₂ (cc' n) (ι' n) (κ' n)
      (a' n) (b' n) (ha' n) (hb' n) (vk' n) (hvk₁' n) (hvk₂' n) Φ (hΦ n) q i j α β xx yy
      hqx hqy hax hby v hv₁ hv₂ (c'' n) (a'' n) (ha'' n))

end Uniform

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
