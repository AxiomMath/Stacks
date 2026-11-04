module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Identifying two adic completions of modules level by level

An element of `AdicCompletion I M` is a compatible family of elements of the infinitesimal
neighbourhoods `M ⧸ IⁿM`. So a family of equivalences of those neighbourhoods, compatible with
the transition maps, is already an equivalence of the completions, and nothing more than the
compatibility is needed: the two modules may live over *different* rings, carrying *different*
ideals.

That is the module-level counterpart of `adicCompletionAlgEquivOfQuotientEquiv`, and it is what
identifies the completed stalk of a coherent adic system with the completion of a localization:
the two sides are localizations of the same level quotients, at corresponding multiplicative
sets, and the identification of the completions is assembled from the identifications of the
levels.

## Main definitions

* `AdicCompletion.addEquivOfQuotientEquiv` — compatible additive equivalences of all the
  infinitesimal neighbourhoods, of modules over possibly different rings, induce an additive
  equivalence of the adic completions.
* `AdicCompletion.linearEquivOfQuotientEquiv` — the same over one base ring, where the
  equivalence is linear.

## Main results

* `AdicCompletion.val_addEquivOfQuotientEquiv` — the level-`n` component of the equivalence is
  the given level-`n` equivalence. This is the clause the construction exists to have.
* `AdicCompletion.eq_addEquivOfQuotientEquiv_of_val` — that clause determines the equivalence.
* `AdicCompletion.addEquivOfQuotientEquiv_smul` — the equivalence is semilinear over any ring
  equivalence whose level-`n` reductions make the given equivalences semilinear. This is how
  the construction is used when the two sides are modules over different rings: the ring
  equivalence is named separately, and this says the module equivalence lies over it.

## Implementation notes

The construction is written directly on the subtype `AdicCompletion`, rather than through
`AdicCompletion.lift`, because the two sides are modules over different rings and `lift` is
linear over one of them. The linearity that does hold is recorded by the clauses instead:
`linearEquivOfQuotientEquiv` in the one-ring case, and `addEquivOfQuotientEquiv_smul` in
general.

No declaration here carries a `stacks` attribute: this is the substrate on which comparisons of
adic completions of modules are phrased, not the content of a tag.
-/

@[expose] public noncomputable section

namespace AdicCompletion

section Quotients

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]
  (I : Ideal R) (J : Ideal S)

variable (e : ∀ n : ℕ, (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃+ (N ⧸ (J ^ n • ⊤ : Submodule S N)))
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
    transitionMap J N h (e n x) = e m (transitionMap I M h x))

/-- Compatible additive equivalences of all the infinitesimal neighbourhoods induce an additive
equivalence of the adic completions. The two modules need not live over the same ring. -/
def addEquivOfQuotientEquiv : AdicCompletion I M ≃+ AdicCompletion J N where
  toFun x := ⟨fun n => e n (x.val n), fun {m n} h => by
    rw [he h (x.val n), x.property h]⟩
  invFun y := ⟨fun n => (e n).symm (y.val n), fun {m n} h => by
    apply (e m).injective
    rw [(e m).apply_symm_apply, ← he h ((e n).symm (y.val n)), (e n).apply_symm_apply,
      y.property h]⟩
  left_inv x := AdicCompletion.ext fun n => (e n).symm_apply_apply (x.val n)
  right_inv y := AdicCompletion.ext fun n => (e n).apply_symm_apply (y.val n)
  map_add' x y := AdicCompletion.ext fun n => (e n).map_add (x.val n) (y.val n)

/-- **The defining clause**: the level-`n` component of the equivalence is the given level-`n`
equivalence applied to the level-`n` component. -/
@[simp]
theorem val_addEquivOfQuotientEquiv (x : AdicCompletion I M) (n : ℕ) :
    (addEquivOfQuotientEquiv I J e he x).val n = e n (x.val n) :=
  rfl

/-- The level-`n` component of the inverse is the inverse of the level-`n` equivalence. -/
@[simp]
theorem val_addEquivOfQuotientEquiv_symm (y : AdicCompletion J N) (n : ℕ) :
    ((addEquivOfQuotientEquiv I J e he).symm y).val n = (e n).symm (y.val n) :=
  rfl

/-- **The defining clause determines the equivalence**: any map with the same level-`n`
components is it. -/
theorem eq_addEquivOfQuotientEquiv_of_val (F : AdicCompletion I M → AdicCompletion J N)
    (hF : ∀ (n : ℕ) (x : AdicCompletion I M), (F x).val n = e n (x.val n))
    (x : AdicCompletion I M) :
    F x = addEquivOfQuotientEquiv I J e he x :=
  AdicCompletion.ext fun n => hF n x

/-- The equivalence carries the canonical image of `m : M` to the canonical image of its image
under the level maps, whenever those are induced by a single map on representatives. -/
theorem addEquivOfQuotientEquiv_of (f : M → N)
    (hf : ∀ (n : ℕ) (m : M), e n (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m))
    (m : M) :
    addEquivOfQuotientEquiv I J e he (of I M m) = of J N (f m) :=
  AdicCompletion.ext fun n => hf n m

end Quotients

section Semilinear

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]
  (I : Ideal R) (J : Ideal S)
  (e : ∀ n : ℕ, (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃+ (N ⧸ (J ^ n • ⊤ : Submodule S N)))
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
    transitionMap J N h (e n x) = e m (transitionMap I M h x))

/-- **Semilinearity over a ring equivalence.** If a ring equivalence `σ` of the two adic
completions matches the level-`n` equivalences, in the sense that `e n` is semilinear for the
action of the level-`n` component of a scalar, then the induced equivalence of completions is
semilinear over `σ`.

This is the clause that places the equivalence of modules *over* a named equivalence of rings,
which is what makes it usable when the two sides have different base rings. -/
theorem addEquivOfQuotientEquiv_smul (σ : AdicCompletion I R → AdicCompletion J S)
    (hσ : ∀ (n : ℕ) (r : AdicCompletion I R) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
      e n (r.val n • x) = (σ r).val n • e n x)
    (r : AdicCompletion I R) (x : AdicCompletion I M) :
    addEquivOfQuotientEquiv I J e he (r • x) = σ r • addEquivOfQuotientEquiv I J e he x :=
  AdicCompletion.ext fun n => by
    rw [val_addEquivOfQuotientEquiv, smul_eval, smul_eval, val_addEquivOfQuotientEquiv,
      hσ n r (x.val n)]

end Semilinear

section OneRing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N] (I J : Ideal R)

/-- Compatible `R`-linear equivalences of all the infinitesimal neighbourhoods induce an
`R`-linear equivalence of the adic completions. -/
def linearEquivOfQuotientEquiv
    (e : ∀ n : ℕ, (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R] (N ⧸ (J ^ n • ⊤ : Submodule R N)))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
      transitionMap J N h (e n x) = e m (transitionMap I M h x)) :
    AdicCompletion I M ≃ₗ[R] AdicCompletion J N :=
  { addEquivOfQuotientEquiv I J (fun n => (e n).toAddEquiv) he with
    map_smul' r x := AdicCompletion.ext fun n => by
      change (e n) ((r • x).val n) = (r • addEquivOfQuotientEquiv I J _ he x).val n
      rw [val_smul_apply, val_smul_apply, val_addEquivOfQuotientEquiv]
      exact (e n).map_smul r (x.val n) }

/-- **The defining clause** of the `R`-linear version. -/
@[simp]
theorem val_linearEquivOfQuotientEquiv
    (e : ∀ n : ℕ, (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R] (N ⧸ (J ^ n • ⊤ : Submodule R N)))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
      transitionMap J N h (e n x) = e m (transitionMap I M h x))
    (x : AdicCompletion I M) (n : ℕ) :
    (linearEquivOfQuotientEquiv I J e he x).val n = e n (x.val n) :=
  rfl

/-- **That clause determines the `R`-linear version.** -/
theorem eq_linearEquivOfQuotientEquiv_of_val
    (e : ∀ n : ℕ, (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[R] (N ⧸ (J ^ n • ⊤ : Submodule R N)))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
      transitionMap J N h (e n x) = e m (transitionMap I M h x))
    (F : AdicCompletion I M → AdicCompletion J N)
    (hF : ∀ (n : ℕ) (x : AdicCompletion I M), (F x).val n = e n (x.val n))
    (x : AdicCompletion I M) :
    F x = linearEquivOfQuotientEquiv I J e he x :=
  AdicCompletion.ext fun n => hF n x

end OneRing

end AdicCompletion

end
