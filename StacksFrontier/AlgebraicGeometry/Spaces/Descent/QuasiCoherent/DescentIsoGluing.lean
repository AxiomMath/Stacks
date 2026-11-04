module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DescentBaseReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness

/-!
# Gluing a family of isomorphisms of the inverse images of a module along an fpqc covering

Let `N` be an `𝒪_R`-module, let `A` be an algebraic space carrying two morphisms
`c₁, c₂ : A ⟶ R` and let `(c k : Z k ⟶ A)` be an fpqc covering of `A`, the two composites
`c k ≫ c₁` and `c k ≫ c₂` being given names `x k` and `y k`.  A family of isomorphisms
`G k : (x k)^*N ≅ (y k)^*N` whose readings agree on every test space mapping to two members then
glues to an isomorphism `c₁^*N ≅ c₂^*N`.

This is the fullness half of Stacks 04W8 — `AlgebraicGeometry.Space.QuasiCoherentDescent`
`.exists_modulePullback_map_eq_of_isFpqcCovering` — applied to the family and to the family of
inverses, with its faithfulness half
(`…modulePullback_map_injective_of_isFpqcCovering`) making the two descended morphisms mutually
inverse.  What has to be supplied is the pairwise condition of Stacks 04W3, and that is what the
agreement of the readings gives.

Applied to a two-leg covering of `R ×_X R` and to the readings of a descent datum, this is the
pairwise isomorphism of the descent datum of `N` relative to the one-member family `{ρ}` — the
transitivity of effective descent.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.unreadIso` transports an isomorphism of the
  inverse images of `N` along the two composites back to an isomorphism of the inverse images
  along `c k` of the two inverse images of `N`, which is the shape the pairwise condition and
  the descent statement are written at.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.mapIso_unreadIso` and `…comp_unreadIso`: the
  reading of the inverse image of a transport is the transport of the reading, as an equality of
  isomorphisms and on morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.ReadingsAgree` is the agreement of the readings,
  and `…canonicalComparison_naturality_unreadIso` and `…isPairwiseCompatible_unreadIso`: **a
  family whose readings agree satisfies the pairwise condition of Stacks 04W3.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readingsAgree_mk` and `…isPairwiseCompatible_mk`
  restate those two conditions at a variable family, so that they are instantiated rather than
  proved.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_mapIso_eq_unreadIso`: **the family
  glues**, to an isomorphism whose inverse image along each member of the covering is the given
  transport.

## Implementation notes

The readings on the two sides of the pairwise condition are taken at one named morphism `e` into
`A`: the two spellings `pairFst ≫ c k` and `pairSnd ≫ c k'` of that morphism are only
propositionally equal, and `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison`
carries that equality inside itself, so both sides are written at the first spelling and nothing
is transported.

The reading on morphisms is written out as a composite of the two comparisons, and **not** as
`AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm`, which is the same morphism and
whose consumer `…canonicalComparison_naturality_of_restrictForm_eq` would supply the pairwise
condition outright: at these types unfolding that reading is a kernel deterministic
timeout, while the composite written out costs nothing.  What replaces that consumer is
`CategoryTheory.Iso.conj_comp_eq_comp_conj`, the same cancellation at a variable category.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **Two morphisms whose conjugates by the comparisons of two factorizations of one morphism
agree are intertwined by the comparisons.**  The two comparisons are given in the shape
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_eq_pullbackComparison`
produces them, as a composite of the inverse of one factorization's comparison with the other's.

Everything is a named morphism at a variable category, so a consumer whose morphisms are
comparisons of inverse images of modules on an algebraic space instantiates it with no
reduction; the same cancellation performed at those types asks the kernel for a delta-iota step
underneath a `≫`, which is a deterministic timeout. -/
theorem conj_comp_eq_comp_conj {A B B' D E E' : C} {Ps : A ≅ B} {Pt : A ≅ B'} {Qs : D ≅ E}
    {Qt : D ≅ E'} {C₁ : B ≅ B'} {C₂ : E ≅ E'} {uk : B ⟶ E} {uk' : B' ⟶ E'} (V : A ⟶ D)
    (h₁ : C₁ = Ps.symm ≪≫ Pt) (h₂ : C₂ = Qs.symm ≪≫ Qt)
    (hk : Ps.hom ≫ uk ≫ Qs.inv = V) (hk' : Pt.hom ≫ uk' ≫ Qt.inv = V) :
    uk ≫ C₂.hom = C₁.hom ≫ uk' := by
  have euk : uk = Ps.inv ≫ V ≫ Qs.hom := by
    rw [← hk]
    simp
  have euk' : uk' = Pt.inv ≫ V ≫ Qt.hom := by
    rw [← hk']
    simp
  subst h₁
  subst h₂
  rw [euk, euk']
  simp

end CategoryTheory.Iso

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Gluing

variable {R : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS R.1 R.2)
  {A : AlgebraicSpaces B S hS} (c₁ c₂ : A ⟶ R)

/-- An isomorphism of the inverse images of `N` along the two composites `q ≫ c₁` and `q ≫ c₂`,
transported to an isomorphism of the inverse images along `q` of the two inverse images of
`N`. -/
def unreadIso {T : AlgebraicSpaces B S hS} (q : T ⟶ A) (x y : T ⟶ R)
    (hx : q ≫ c₁ = x) (hy : q ≫ c₂ = y)
    (G : (modulePullback B S hS x).obj N ≅ (modulePullback B S hS y).obj N) :
    (modulePullback B S hS q).obj ((modulePullback B S hS c₁).obj N) ≅
      (modulePullback B S hS q).obj ((modulePullback B S hS c₂).obj N) :=
  (pullbackComparison B S hS q c₁ x hx N).symm ≪≫ G ≪≫
    pullbackComparison B S hS q c₂ y hy N

/-- **The reading at a morphism into `A` of the inverse image of a transported isomorphism is
the transport of its reading.**  Both sides are read at one named morphism `e` into `A`, which
is where the two spellings of that morphism on the two sides of a pairwise condition are
reconciled. -/
theorem mapIso_unreadIso {T P : AlgebraicSpaces B S hS} (p : T ⟶ A) (x y : T ⟶ R)
    (hx : p ≫ c₁ = x) (hy : p ≫ c₂ = y)
    (G : (modulePullback B S hS x).obj N ≅ (modulePullback B S hS y).obj N)
    (q : P ⟶ T) (e : P ⟶ A) (he : q ≫ p = e) (x' y' : P ⟶ R) (hx' : e ≫ c₁ = x')
    (hy' : e ≫ c₂ = y') (hqx : q ≫ x = x') (hqy : q ≫ y = y') :
    pullbackComparison B S hS q p e he ((modulePullback B S hS c₁).obj N) ≪≫
        (modulePullback B S hS q).mapIso (unreadIso B S hS N c₁ c₂ p x y hx hy G) ≪≫
        (pullbackComparison B S hS q p e he ((modulePullback B S hS c₂).obj N)).symm =
      unreadIso B S hS N c₁ c₂ e x' y' hx' hy'
        (pullbackComparison B S hS q x x' hqx N ≪≫
          (modulePullback B S hS q).mapIso G ≪≫
          (pullbackComparison B S hS q y y' hqy N).symm) := by
  rw [unreadIso, unreadIso]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  rw [modulePullback_mapIso_pullbackComparison B S hS q p c₁ x hx e he x' hx' hqx N,
    modulePullback_mapIso_pullbackComparison B S hS q p c₂ y hy e he y' hy' hqy N]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl]

/-- **The reading on morphisms**: `…mapIso_unreadIso` read through
`CategoryTheory.Iso.trans_hom`. -/
theorem comp_unreadIso {T P : AlgebraicSpaces B S hS} (p : T ⟶ A) (x y : T ⟶ R)
    (hx : p ≫ c₁ = x) (hy : p ≫ c₂ = y)
    (G : (modulePullback B S hS x).obj N ≅ (modulePullback B S hS y).obj N)
    (q : P ⟶ T) (e : P ⟶ A) (he : q ≫ p = e) (x' y' : P ⟶ R) (hx' : e ≫ c₁ = x')
    (hy' : e ≫ c₂ = y') (hqx : q ≫ x = x') (hqy : q ≫ y = y') :
    (pullbackComparison B S hS q p e he ((modulePullback B S hS c₁).obj N)).hom ≫
        (modulePullback B S hS q).map (unreadIso B S hS N c₁ c₂ p x y hx hy G).hom ≫
        (pullbackComparison B S hS q p e he ((modulePullback B S hS c₂).obj N)).inv =
      (unreadIso B S hS N c₁ c₂ e x' y' hx' hy'
        (pullbackComparison B S hS q x x' hqx N ≪≫
          (modulePullback B S hS q).mapIso G ≪≫
          (pullbackComparison B S hS q y y' hqy N).symm)).hom := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    using congrArg Iso.hom
      (mapIso_unreadIso B S hS N c₁ c₂ p x y hx hy G q e he x' y' hx' hy' hqx hqy)

variable {I : Type v} (Z : I → AlgebraicSpaces B S hS) (c : ∀ k, Z k ⟶ A)
  (x y : ∀ k, Z k ⟶ R) (hx : ∀ k, c k ≫ c₁ = x k) (hy : ∀ k, c k ≫ c₂ = y k)
  (G : ∀ k, (modulePullback B S hS (x k)).obj N ≅ (modulePullback B S hS (y k)).obj N)

/-- The agreement of the readings of a family of isomorphisms of the inverse images of `N`
along the two legs of a family over `A`.  It is named so that the two statements it is the
hypothesis of, and the proof that joins them, share one spelling of it. -/
def ReadingsAgree : Prop :=
  ∀ (k k' : I) (P : AlgebraicSpaces B S hS) (s : P ⟶ Z k) (t : P ⟶ Z k')
      (x' y' : P ⟶ R) (hx₁ : s ≫ x k = x') (hy₁ : s ≫ y k = y')
      (hx₂ : t ≫ x k' = x') (hy₂ : t ≫ y k' = y'),
    pullbackComparison B S hS s (x k) x' hx₁ N ≪≫
        (modulePullback B S hS s).mapIso (G k) ≪≫
        (pullbackComparison B S hS s (y k) y' hy₁ N).symm =
      pullbackComparison B S hS t (x k') x' hx₂ N ≪≫
        (modulePullback B S hS t).mapIso (G k') ≪≫
        (pullbackComparison B S hS t (y k') y' hy₂ N).symm

/-- **The agreement of the readings, restated at a variable family.**  Like
`…isPairwiseCompatible_mk` it exists to be instantiated rather than proved: at these types the
kernel does not finish unfolding a definition whose statement is this equation at a concrete
family of readings. -/
theorem readingsAgree_mk
    (h : ∀ (k k' : I) (P : AlgebraicSpaces B S hS) (s : P ⟶ Z k) (t : P ⟶ Z k')
        (x' y' : P ⟶ R) (hx₁ : s ≫ x k = x') (hy₁ : s ≫ y k = y')
        (hx₂ : t ≫ x k' = x') (hy₂ : t ≫ y k' = y'),
      pullbackComparison B S hS s (x k) x' hx₁ N ≪≫
          (modulePullback B S hS s).mapIso (G k) ≪≫
          (pullbackComparison B S hS s (y k) y' hy₁ N).symm =
        pullbackComparison B S hS t (x k') x' hx₂ N ≪≫
          (modulePullback B S hS t).mapIso (G k') ≪≫
          (pullbackComparison B S hS t (y k') y' hy₂ N).symm) :
    ReadingsAgree B S hS N Z x y G :=
  h

/-- **The pairwise condition of Stacks 04W3 at one pair of indices, for a family whose readings
agree.**  This is `…comp_unreadIso` on both sides and the agreement of the readings between
them, with the canonical comparison of Stacks 04W5 written as the composite of the two
comparisons for the leg `pairFst ≫ c k` by `…canonicalComparison_eq_pullbackComparison` and
`CategoryTheory.Iso.conj_comp_eq_comp_conj` performing the cancellation. -/
theorem canonicalComparison_naturality_unreadIso (hG : ReadingsAgree B S hS N Z x y G)
    (k k' : I) :
    (modulePullback B S hS (pairFst B S hS Z c k k')).map
          (unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)).hom ≫
        (canonicalComparison (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
          (pair_condition B S hS Z c k k') ((modulePullback B S hS c₂).obj N)).hom =
      (canonicalComparison (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
          (pair_condition B S hS Z c k k') ((modulePullback B S hS c₁).obj N)).hom ≫
        (modulePullback B S hS (pairSnd B S hS Z c k k')).map
          (unreadIso B S hS N c₁ c₂ (c k') (x k') (y k') (hx k') (hy k') (G k')).hom := by
  have hx₁ : pairFst B S hS Z c k k' ≫ x k = (pairFst B S hS Z c k k' ≫ c k) ≫ c₁ := by
    rw [← hx k, ← Category.assoc]
  have hy₁ : pairFst B S hS Z c k k' ≫ y k = (pairFst B S hS Z c k k' ≫ c k) ≫ c₂ := by
    rw [← hy k, ← Category.assoc]
  have hx₂ : pairSnd B S hS Z c k k' ≫ x k' = (pairFst B S hS Z c k k' ≫ c k) ≫ c₁ := by
    rw [← hx k', ← Category.assoc, pair_condition B S hS Z c k k']
  have hy₂ : pairSnd B S hS Z c k k' ≫ y k' = (pairFst B S hS Z c k k' ≫ c k) ≫ c₂ := by
    rw [← hy k', ← Category.assoc, pair_condition B S hS Z c k k']
  have hcomp := fun M => canonicalComparison_eq_pullbackComparison B S hS
    (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
    (pair_condition B S hS Z c k k') (pairFst B S hS Z c k k' ≫ c k) rfl
    (pair_condition B S hS Z c k k').symm M
  refine Iso.conj_comp_eq_comp_conj _ (hcomp _) (hcomp _)
    (comp_unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)
      (pairFst B S hS Z c k k') (pairFst B S hS Z c k k' ≫ c k) rfl
      ((pairFst B S hS Z c k k' ≫ c k) ≫ c₁) ((pairFst B S hS Z c k k' ≫ c k) ≫ c₂) rfl rfl
      hx₁ hy₁) ?_
  rw [comp_unreadIso B S hS N c₁ c₂ (c k') (x k') (y k') (hx k') (hy k') (G k')
      (pairSnd B S hS Z c k k') (pairFst B S hS Z c k k' ≫ c k)
      (pair_condition B S hS Z c k k').symm
      ((pairFst B S hS Z c k k' ≫ c k) ≫ c₁) ((pairFst B S hS Z c k k' ≫ c k) ≫ c₂) rfl rfl
      hx₂ hy₂,
    hG k k' (pair B S hS Z c k k') (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k')
      ((pairFst B S hS Z c k k' ≫ c k) ≫ c₁) ((pairFst B S hS Z c k k' ≫ c k) ≫ c₂)
      hx₁ hy₁ hx₂ hy₂]

end Gluing

section Compatible

variable {A : AlgebraicSpaces B S hS} {I : Type v} (Z : I → AlgebraicSpaces B S hS)
  (c : ∀ k, Z k ⟶ A)

/-- **The pairwise condition of Stacks 04W3, restated at a variable family of morphisms and
variable modules.**

It is the definition and nothing else.  It exists because it has to be *instantiated* and not
proved: a declaration whose statement is
`AlgebraicGeometry.Space.QuasiCoherentDescent.IsPairwiseCompatible` at a concrete family of
isomorphisms of iterated inverse images, proved by introducing the two indices, is a
kernel deterministic timeout, while instantiating this one at that family is free — the
substitution asks for no conversion at all. -/
theorem isPairwiseCompatible_mk {M M' : Modules.{u, u} B S hS A.1 A.2}
    (w : ∀ k, (modulePullback B S hS (c k)).obj M ⟶ (modulePullback B S hS (c k)).obj M')
    (h : ∀ k k', (modulePullback B S hS (pairFst B S hS Z c k k')).map (w k) ≫
        (canonicalComparison (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
          (pair_condition B S hS Z c k k') M').hom =
      (canonicalComparison (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
          (pair_condition B S hS Z c k k') M).hom ≫
        (modulePullback B S hS (pairSnd B S hS Z c k k')).map (w k')) :
    IsPairwiseCompatible B S hS Z c w :=
  h

end Compatible

section Glued

variable {R : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS R.1 R.2)
  {A : AlgebraicSpaces B S hS} (c₁ c₂ : A ⟶ R)
  {I : Type v} (Z : I → AlgebraicSpaces B S hS) (c : ∀ k, Z k ⟶ A)
  (x y : ∀ k, Z k ⟶ R) (hx : ∀ k, c k ≫ c₁ = x k) (hy : ∀ k, c k ≫ c₂ = y k)
  (G : ∀ k, (modulePullback B S hS (x k)).obj N ≅ (modulePullback B S hS (y k)).obj N)

/-- **A family of isomorphisms of the inverse images of `N` along the two legs of a family over
`A`, whose readings agree on every test space mapping to two of its members, satisfies the
pairwise condition of Stacks 04W3** for the two inverse images of `N` to `A`. -/
theorem isPairwiseCompatible_unreadIso (hG : ReadingsAgree B S hS N Z x y G) :
    IsPairwiseCompatible B S hS Z c
      (fun k => (unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)).hom) :=
  isPairwiseCompatible_mk B S hS Z c _ fun k k' =>
    canonicalComparison_naturality_unreadIso B S hS N c₁ c₂ Z c x y hx hy G hG k k'

/-- The inverses of such a family satisfy the pairwise condition too, by the naturality of the
inverse of an isomorphism. -/
theorem isPairwiseCompatible_unreadIso_inv (hG : ReadingsAgree B S hS N Z x y G) :
    IsPairwiseCompatible B S hS Z c
      (fun k => (unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)).inv) :=
  isPairwiseCompatible_mk B S hS Z c _ fun k k' =>
    inv_naturality
      ((modulePullback B S hS (pairFst B S hS Z c k k')).mapIso
        (unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)))
      ((modulePullback B S hS (pairSnd B S hS Z c k k')).mapIso
        (unreadIso B S hS N c₁ c₂ (c k') (x k') (y k') (hx k') (hy k') (G k')))
      (canonicalComparison (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
        (pair_condition B S hS Z c k k') ((modulePullback B S hS c₁).obj N)).hom
      (canonicalComparison (pairFst B S hS Z c k k') (pairSnd B S hS Z c k k') (c k) (c k')
        (pair_condition B S hS Z c k k') ((modulePullback B S hS c₂).obj N)).hom
      (canonicalComparison_naturality_unreadIso B S hS N c₁ c₂ Z c x y hx hy G hG k k')

/-- **A family of isomorphisms of the inverse images of `N` along the two legs of an fpqc
covering of `A`, whose readings agree, glues to an isomorphism of the two inverse images of `N`
to `A`.**

The two halves of the full-faithfulness clause of Stacks 04W8 are what this rests on: fullness
descends the family and the family of inverses, and faithfulness identifies the two composites
with the identities. -/
theorem exists_mapIso_eq_unreadIso (hN : N.IsQuasicoherentOnSite)
    (hcov : IsFpqcCovering B S hS fun k => (c k).hom)
    (hG : ReadingsAgree B S hS N Z x y G) :
    ∃ Φ : (modulePullback B S hS c₁).obj N ≅ (modulePullback B S hS c₂).obj N,
      ∀ k, (modulePullback B S hS (c k)).mapIso Φ =
        unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k) := by
  obtain ⟨φ, hφ⟩ := exists_modulePullback_map_eq_of_isFpqcCovering B S hS
    (reprFpqcHomSurjective.{u, v} B S hS) Z c hcov
    (fun k => (unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)).hom)
    (isPairwiseCompatible_unreadIso B S hS N c₁ c₂ Z c x y hx hy G hG)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c₁ N hN)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c₂ N hN)
  obtain ⟨χ, hχ⟩ := exists_modulePullback_map_eq_of_isFpqcCovering B S hS
    (reprFpqcHomSurjective.{u, v} B S hS) Z c hcov
    (fun k => (unreadIso B S hS N c₁ c₂ (c k) (x k) (y k) (hx k) (hy k) (G k)).inv)
    (isPairwiseCompatible_unreadIso_inv B S hS N c₁ c₂ Z c x y hx hy G hG)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c₂ N hN)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c₁ N hN)
  refine ⟨⟨φ, χ, ?_, ?_⟩, fun k => Iso.ext (hφ k)⟩ <;>
    refine modulePullback_map_injective_of_isFpqcCovering B S hS
      (reprFpqcHomInjective B S hS) Z c hcov _ _ fun k => ?_ <;>
    simp [hφ k, hχ k]

end Glued


end AlgebraicGeometry.Space.QuasiCoherentDescent

end
