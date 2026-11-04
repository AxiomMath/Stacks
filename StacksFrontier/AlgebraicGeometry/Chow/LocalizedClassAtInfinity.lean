module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent

/-!
# The factorization of Stacks 0F9K, on cap operations

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `Z ⊆ X` be a closed subscheme, and let `W_∞ ⟶ X` be the fibre at
infinity of a proper `b : W ⟶ 𝐏¹_X` which is an isomorphism over `𝐀¹_X`, with `E = W_∞ ×_X Z`.
Stacks 0F9K defines its classes `P'_p(Q)`, resp. `c'_p(Q) ∈ A^p(Z ⟶ X)` by the factorization

  `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C`,

with `C ∈ A⁰(W_∞ ⟶ X)` the class of Stacks 0F9J and `c'_p(Q|_E) ∈ A^p(E ⟶ W_∞)` that of
Stacks 0F9H. This module states that factorization on the cap operation of every test scheme, for
arbitrary classes in the three slots, and proves the chain of equalities of the proof of
Stacks 0FAU for it: if `g_{∞,*} ∘ C' = C` and the middle factor over a modification is the
restriction of the one over `W`, then the two factorized classes agree.

## Main definitions

* `Stacks.Chow.IsLocalizedClassAtInfinity` — the factorization of Stacks 0F9K, read on the cap
  operation of each test scheme.

## Main results

* `Stacks.Chow.eq_of_isLocalizedClassAtInfinity_of_modification` — the invariance argument of
  Stacks 0FAU, on cap operations.

## Implementation notes

The base change of `E ⟶ Z` to a test scheme, the base change of `W'_∞ ⟶ W_∞` and the
identification of the two fibre products are parameters, with the compatibilities the argument
uses.

## References

* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0FAU](https://stacks.math.columbia.edu/tag/0FAU)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The factorization of Stacks 0F9K -/

/-- **The factorization of Stacks 0F9K.** The assertion that a bivariant class
`c'_p(Q) ∈ A^p(Z ⟶ X)` is `(E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C`: on every test scheme `t : T ⟶ X`
locally of finite type and in every degree, its cap operation is "cap with `C`, cap with
`c'_p(Q|_E)`, push forward along the base change of `E ⟶ Z`".

The degrees: capping with `C` leaves `k - 0`, capping with `c'_p(Q|_E)` leaves `k - 0 - p`, and
`Stacks.Chow.chowGroupDegreeEquiv` reads that as the degree `k - p` in which a class of degree
`p` caps. -/
def IsLocalizedClassAtInfinity (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Z WInf E : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sWInf : WInf ⟶ C.S)
    [LocallyOfFiniteType sWInf] (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (iZ : Z ⟶ X)
    [LocallyOfFiniteType iZ] (pInf : WInf ⟶ X) [LocallyOfFiniteType pInf]
    (hpInf : pInf ≫ sX = sWInf) (iE : E ⟶ WInf) [LocallyOfFiniteType iE]
    (hiE : iE ≫ sWInf = sE) (p : ℤ)
    (dsc : ∀ {T : Scheme.{u}} (t : T ⟶ X), [LocallyOfFiniteType t] →
      pullback iE (pullback.fst pInf t) ⟶ pullback iZ t)
    (hdsc : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t], IsProper (dsc t))
    (hdscComp : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      dsc t ≫ (pullback.fst iZ t ≫ (iZ ≫ sX)) = pullback.fst iE (pullback.fst pInf t) ≫ sE)
    (cC : BivariantClass C G sWInf sX pInf hpInf 0)
    (cE : BivariantClass C G sE sWInf iE hiE p)
    (cZ : BivariantClass C G (iZ ≫ sX) sX iZ rfl p) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
    letI := hdsc t
    ∀ (k : ℤ) (α : chowGroup C (t ≫ sX) k),
      cZ.cap t k α =
        chowGroupDegreeEquiv C (pullback.fst iZ t ≫ (iZ ≫ sX)) (by ring : k - 0 - p = k - p)
          (properChowPushforward C (pullback.fst iE (pullback.fst pInf t) ≫ sE)
            (pullback.fst iZ t ≫ (iZ ≫ sX)) (dsc t) (hdscComp t) (k - 0 - p)
            (properPushforwardDescends C _ _ _ _ _)
            (cE.cap (pullback.fst pInf t) (k - 0) (cC.cap t k α)))

/-! ### Invariance under a modification of the fibre at infinity -/

/-- **The invariance argument of Stacks 0FAU, on cap operations.** Let `g_∞ : W'_∞ ⟶ W_∞` be
proper over `X`, and let `c'_p(Q) = (E ⟶ Z)_* ∘ c'_p(Q|_E) ∘ C` and
`c'_p(Q') = (E' ⟶ Z)_* ∘ c'_p(Q'|_{E'}) ∘ C'` be two classes with the factorization of
Stacks 0F9K. Suppose that

* `g_{∞,*} ∘ C' = C`, read on the cap operation of each test scheme through the base change
  `m` of `g_∞` (this is Stacks 0FAQ);
* `c'_p(Q'|_{E'})` is the restriction of `c'_p(Q|_E)` along `g_∞` (Remark 0F9Z), read on the
  test schemes `W'_∞ ×_X T` through an identification `ψ` of the two fibre products;
* the base changes of `E' ⟶ Z`, of `E ⟶ Z` and of `E' ⟶ E` are compatible.

Then `c'_p(Q') = c'_p(Q)`. -/
theorem eq_of_isLocalizedClassAtInfinity_of_modification (C : ChowSituation.{u})
    (G : GysinSystem C) {X Z WInf E WInf' E' : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sWInf : WInf ⟶ C.S) [LocallyOfFiniteType sWInf] (sE : E ⟶ C.S)
    [LocallyOfFiniteType sE] (sWInf' : WInf' ⟶ C.S) [LocallyOfFiniteType sWInf']
    (sE' : E' ⟶ C.S) [LocallyOfFiniteType sE'] (iZ : Z ⟶ X) [LocallyOfFiniteType iZ]
    (pInf : WInf ⟶ X) [LocallyOfFiniteType pInf] (hpInf : pInf ≫ sX = sWInf)
    (iE : E ⟶ WInf) [LocallyOfFiniteType iE] (hiE : iE ≫ sWInf = sE)
    (pInf' : WInf' ⟶ X) [LocallyOfFiniteType pInf'] (hpInf' : pInf' ≫ sX = sWInf')
    (iE' : E' ⟶ WInf') [LocallyOfFiniteType iE'] (hiE' : iE' ≫ sWInf' = sE')
    (gInf : WInf' ⟶ WInf) [LocallyOfFiniteType gInf] (hg : gInf ≫ pInf = pInf') (p : ℤ)
    (dsc : ∀ {T : Scheme.{u}} (t : T ⟶ X), [LocallyOfFiniteType t] →
      pullback iE (pullback.fst pInf t) ⟶ pullback iZ t)
    (hdsc : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t], IsProper (dsc t))
    (hdscComp : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      dsc t ≫ (pullback.fst iZ t ≫ (iZ ≫ sX)) = pullback.fst iE (pullback.fst pInf t) ≫ sE)
    (dsc' : ∀ {T : Scheme.{u}} (t : T ⟶ X), [LocallyOfFiniteType t] →
      pullback iE' (pullback.fst pInf' t) ⟶ pullback iZ t)
    (hdsc' : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t], IsProper (dsc' t))
    (hdscComp' : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      dsc' t ≫ (pullback.fst iZ t ≫ (iZ ≫ sX)) = pullback.fst iE' (pullback.fst pInf' t) ≫ sE')
    (m : ∀ {T : Scheme.{u}} (t : T ⟶ X), [LocallyOfFiniteType t] →
      pullback pInf' t ⟶ pullback pInf t)
    (hm : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t], IsProper (m t))
    (hmFst : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      m t ≫ pullback.fst pInf t = pullback.fst pInf' t ≫ gInf)
    (ψ : ∀ {T : Scheme.{u}} (t : T ⟶ X), [LocallyOfFiniteType t] →
      pullback iE (pullback.fst pInf' t ≫ gInf) ≅ pullback iE' (pullback.fst pInf' t))
    (hψ : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      (ψ t).hom ≫ (pullback.fst iE' (pullback.fst pInf' t) ≫ sE') =
        pullback.fst iE (pullback.fst pInf' t ≫ gInf) ≫ sE)
    (cmp : ∀ {T : Scheme.{u}} (t : T ⟶ X), [LocallyOfFiniteType t] →
      pullback iE (pullback.fst pInf' t ≫ gInf) ⟶ pullback iE (pullback.fst pInf t))
    (hcmpSq : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      IsPullback (pullback.snd iE (pullback.fst pInf' t ≫ gInf)) (cmp t) (m t)
        (pullback.snd iE (pullback.fst pInf t)))
    (hcmpFst : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      cmp t ≫ pullback.fst iE (pullback.fst pInf t) =
        pullback.fst iE (pullback.fst pInf' t ≫ gInf))
    (hcompat : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t],
      (ψ t).hom ≫ dsc' t = cmp t ≫ dsc t)
    {cC : BivariantClass C G sWInf sX pInf hpInf 0} {cE : BivariantClass C G sE sWInf iE hiE p}
    {cZ : BivariantClass C G (iZ ≫ sX) sX iZ rfl p}
    {cC' : BivariantClass C G sWInf' sX pInf' hpInf' 0}
    {cE' : BivariantClass C G sE' sWInf' iE' hiE' p}
    {cZ' : BivariantClass C G (iZ ≫ sX) sX iZ rfl p}
    (hpush : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX) k),
      letI := hm t
      cC.cap t k α =
        properChowPushforward C (pullback.fst pInf' t ≫ sWInf') (pullback.fst pInf t ≫ sWInf)
          (m t) (by rw [← Category.assoc, hmFst t, Category.assoc, ← hpInf, ← hpInf',
            ← Category.assoc gInf, hg]) (k - 0)
          (properPushforwardDescends C _ _ _ _ _) (cC'.cap t k α))
    (hrest : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
      (x : chowGroup C (pullback.fst pInf' t ≫ sWInf') k),
      cE'.cap (pullback.fst pInf' t) k x =
        chowPushforwardOfIso C (pullback.fst iE (pullback.fst pInf' t ≫ gInf) ≫ sE)
          (pullback.fst iE' (pullback.fst pInf' t) ≫ sE') (ψ t).hom (hψ t) (k - p)
          (cE.cap (pullback.fst pInf' t ≫ gInf) k
            (chowGroupCongr C (by rw [Category.assoc, ← hpInf, ← hpInf', ← Category.assoc gInf,
              hg]) k x)))
    (hZ : IsLocalizedClassAtInfinity C G sX sWInf sE iZ pInf hpInf iE hiE p dsc hdsc hdscComp
      cC cE cZ)
    (hZ' : IsLocalizedClassAtInfinity C G sX sWInf' sE' iZ pInf' hpInf' iE' hiE' p dsc' hdsc'
      hdscComp' cC' cE' cZ') :
    cZ' = cZ := by
  refine BivariantClass.ext C G (iZ ≫ sX) sX iZ rfl p ?_
  intro T t _ k α
  let : IsProper (dsc t) := hdsc t
  let : IsProper (dsc' t) := hdsc' t
  let : IsProper (m t) := hm t
  let : IsProper (cmp t) :=
    MorphismProperty.of_isPullback (hcmpSq t) (P := @IsProper) inferInstance
  have hs : pullback.fst pInf' t ≫ sWInf' = (pullback.fst pInf' t ≫ gInf) ≫ sWInf := by
    rw [Category.assoc, ← hpInf, ← hpInf', ← Category.assoc gInf, hg]
  rw [hZ' t k α, hZ t k α, hrest t (k - 0) (cC'.cap t k α), hpush t k α]
  refine congrArg (chowGroupDegreeEquiv C (pullback.fst iZ t ≫ (iZ ≫ sX)) _) ?_
  have hmb : m t ≫ (pullback.fst pInf t ≫ sWInf) = (pullback.fst pInf' t ≫ gInf) ≫ sWInf := by
    rw [← Category.assoc, hmFst t]
  have hnat := cE.proper_naturality_of_test_eq (pullback.fst pInf t) (m t)
    (pullback.fst pInf' t ≫ gInf) (hmFst t) (cmp t) (hcmpSq t) (hcmpFst t) (k - 0) hmb
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (chowGroupCongr C hs (k - 0) (cC'.cap t k α))
  have hcongr : properChowPushforward C (pullback.fst pInf' t ≫ sWInf')
        (pullback.fst pInf t ≫ sWInf) (m t)
        (hmb.trans hs.symm) (k - 0)
        (properPushforwardDescends C _ _ _ _ _) (cC'.cap t k α) =
      properChowPushforward C ((pullback.fst pInf' t ≫ gInf) ≫ sWInf)
        (pullback.fst pInf t ≫ sWInf) (m t) hmb (k - 0)
        (properPushforwardDescends C _ _ _ _ _) (chowGroupCongr C hs (k - 0) (cC'.cap t k α)) :=
    properChowPushforward_chowGroupCongr C hs rfl (m t) _ hmb (k - 0)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (cC'.cap t k α)
  rw [hcongr, hnat]
  exact properChowPushforward_comp_eq C
    (pullback.fst iE (pullback.fst pInf' t ≫ gInf) ≫ sE)
    (pullback.fst iE' (pullback.fst pInf' t) ≫ sE')
    (pullback.fst iE (pullback.fst pInf t) ≫ sE) (pullback.fst iZ t ≫ (iZ ≫ sX))
    (ψ t).hom (dsc' t) (cmp t) (dsc t) (hcompat t) (hψ t) (hdscComp' t)
    (by rw [← Category.assoc, hcmpFst t]) (hdscComp t) (k - 0 - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _

end Stacks.Chow

end
