module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AlphaPCoverDegree

/-!
# The local algebraic normal form of an iterated `α_p`-cover, and its degree

A composition `X' = X_n ⟶ ⋯ ⟶ X_1 ⟶ X_0 = X` of `α_p`-covers is, on global sections, a tower of
ring extensions

`C = R_0 ⟶ R_1 ⟶ ⋯ ⟶ R_n`,  `R_{i+1} ≅ R_i[z]/(z ^ p - c_i)`,  `c_i ∈ R_i`,

starting at `C = Γ(X, ⊤)` and ending at `Γ(X', ⊤)`.  This module packages such towers as an
inductive datum `AlgebraicGeometry.AlphaPChain`, proves that every composition of `α_p`-covers
has such a normal form, that the affine opens over which an iterated `α_p`-cover is a composition
of `α_p`-covers form a basis of the topology of the target, and that over such an open the length
`n` of the chain determines a given constant degree `q` as `q = p ^ n`.  This is the local
algebraic input of [Stacks, Lemma 60.25.4, Tag 07Q9]: the proof there works on a basis of affine
opens of `X` over which `X' ⟶ X` is a chain of `n` covers `C[z]/(z ^ p - c) / C`, and uses that
the degree `q` of the statement equals `p ^ n`.

## Main definitions

* `AlgebraicGeometry.AlphaPChain p C n` — a chain of `n` successive `α_p`-extensions starting at
  the ring `C`, built from the bottom: a chain over `C` of length `n + 1` is an element `c ∈ C`
  together with a chain of length `n` over `C[z]/(z ^ p - c)`.
* `AlgebraicGeometry.AlphaPChain.top` and `AlgebraicGeometry.AlphaPChain.toTop` — the last ring of
  a chain and the structure map from its first ring.
* `AlgebraicGeometry.HasAlphaPChainNormalForm p f` — for every identification of `Γ(X, ⊤)` with a
  ring `C`, the map `f.appTop` is, up to an isomorphism of `Γ(X', ⊤)`, the structure map of a
  chain over `C`.

## Main results

* `AlgebraicGeometry.AlphaPChain.hasFiniteBasis_toTop` — the last ring of a chain of length `n` is
  free of rank `p ^ n` over the first.
* `AlgebraicGeometry.hasAlphaPChainNormalForm_of_isAlphaPCoverComposite` and
  `AlgebraicGeometry.exists_alphaPChain_of_isAlphaPCoverComposite` — **a composition of
  `α_p`-covers has a chain normal form** over the global sections of its target.
* `AlgebraicGeometry.AlphaPChain.isAlphaPCoverComposite_spec_toTop` and
  `AlgebraicGeometry.isAlphaPCoverComposite_of_alphaPChain` — conversely, the spectrum of a chain
  is a composition of `α_p`-covers, so between affine schemes in characteristic `p` having a
  chain normal form and being a composition of `α_p`-covers are equivalent.
* `AlgebraicGeometry.exists_alphaPChain_app_of_isAlphaPCoverComposite` — the normal form over an
  open `W` of the target, as a chain over `Γ(X, W)` ending at `Γ(X', f ⁻¹ᵁ W)`.
* `AlgebraicGeometry.IsAlphaPCoverComposite.morphismRestrict_of_le` — the restriction of a
  composition of `α_p`-covers over an open `U` to an affine open contained in `U` is again one.
* `AlgebraicGeometry.exists_isAffineOpen_isAlphaPCoverComposite` and
  `AlgebraicGeometry.isBasis_isAlphaPCoverComposite` — **for an iterated `α_p`-cover the affine
  opens over which it is a composition of `α_p`-covers form a basis**, and may be taken inside
  any given neighbourhood of any given point; `AlgebraicGeometry.exists_isAffineOpen_alphaPChain`
  is the same with the chain normal form over `Γ(X, W)`.
* `AlgebraicGeometry.eq_pow_of_hasConstantDegree_of_alphaPChain` — **over a nonempty such open
  with a chain of length `n`, a constant degree `q` of the iterated `α_p`-cover is `p ^ n`.**
* `AlgebraicGeometry.exists_alphaPChain_and_eq_pow_of_hasConstantDegree` — the two together: every
  neighbourhood of every point contains an affine open with a chain normal form whose length `n`
  satisfies `q = p ^ n`.

## Implementation notes

`IsAlphaPCoverComposite` peels its `α_p`-covers off from the source, whereas a chain is built
from the bottom ring `C` upwards.  The normal form is therefore proved in the dual form
"if `u : W ⟶ X'` has a chain normal form over `Γ(X', ⊤)`, so does `u ≫ f` over `Γ(X, ⊤)`", by
induction on `f`, and only then specialised to `u = 𝟙 X'`; and a chain normal form is asked for
over *every* ring `C` identified with `Γ(X, ⊤)`, which is what lets the identification of an
`α_p`-cover with its local model, which holds only up to isomorphisms of source and target, be
absorbed into the chain without transporting chains along ring isomorphisms.

The base change statements `AlgebraicGeometry.IsAlphaPCover.of_isPullback`,
`AlgebraicGeometry.IsAlphaPCoverComposite.of_isPullback` and
`AlgebraicGeometry.HasFiniteBasis.of_isPullback_appTop` used here are those of
`StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCover`.

The degree comparison needs the sections over the open `U` that `HasConstantDegree` provides to
be the sections of an affine scheme; this is where `IsIteratedAlphaPCover` enters, through
`AlgebraicGeometry.isAffineHom_of_isIteratedAlphaPCover`: an iterated `α_p`-cover is an affine
morphism, being one locally on the target.

## References

* [Stacks Project, Section 60.25, Tag 07PZ](https://stacks.math.columbia.edu/tag/07PZ)
* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u v w

namespace AlgebraicGeometry

/-! ### Chains of `α_p`-extensions -/

/-- A chain of `n` successive `α_p`-extensions starting at the ring `C`:
`C = R_0 ⟶ R_1 ⟶ ⋯ ⟶ R_n` with `R_{i+1} = R_i[z]/(z ^ p - c_i)` for elements `c_i ∈ R_i`.  It is
built from the bottom: the empty chain over `C`, or an element `c ∈ C` followed by a chain over
`C[z]/(z ^ p - c)`. -/
inductive AlphaPChain (p : ℕ) : CommRingCat.{u} → ℕ → Type (u + 1)
  /-- The chain of length `0` over `C`. -/
  | nil (C : CommRingCat.{u}) : AlphaPChain p C 0
  /-- The chain `C ⟶ C[z]/(z ^ p - c) ⟶ ⋯` whose first stage adjoins a `p`-th root of `c`. -/
  | cons {C : CommRingCat.{u}} {n : ℕ} (c : C)
      (rest : AlphaPChain p (CommRingCat.of (alphaPAlgebra p C c)) n) : AlphaPChain p C (n + 1)

namespace AlphaPChain

variable {p : ℕ}

/-- The last ring `R_n` of a chain. -/
def top : {C : CommRingCat.{u}} → {n : ℕ} → AlphaPChain p C n → CommRingCat.{u}
  | C, _, nil _ => C
  | _, _, cons _ rest => rest.top

/-- The structure map `C = R_0 ⟶ R_n` of a chain, the composite of its stages. -/
def toTop : {C : CommRingCat.{u}} → {n : ℕ} → (ch : AlphaPChain p C n) → (C ⟶ ch.top)
  | _, _, nil C => 𝟙 C
  | C, _, cons c rest => CommRingCat.ofHom (algebraMap C (alphaPAlgebra p C c)) ≫ rest.toTop

/-- The last ring of the empty chain over `C` is `C`. -/
@[simp]
theorem top_nil (C : CommRingCat.{u}) : (nil (p := p) C).top = C :=
  rfl

/-- The last ring of `cons c rest` is the last ring of `rest`. -/
@[simp]
theorem top_cons {C : CommRingCat.{u}} {n : ℕ} (c : C)
    (rest : AlphaPChain p (CommRingCat.of (alphaPAlgebra p C c)) n) :
    (cons c rest).top = rest.top :=
  rfl

/-- The structure map of the empty chain over `C` is the identity of `C`. -/
@[simp]
theorem toTop_nil (C : CommRingCat.{u}) : (nil (p := p) C).toTop = 𝟙 C :=
  rfl

/-- The structure map of `cons c rest` is the inclusion `C ⟶ C[z]/(z ^ p - c)` followed by the
structure map of `rest`. -/
@[simp]
theorem toTop_cons {C : CommRingCat.{u}} {n : ℕ} (c : C)
    (rest : AlphaPChain p (CommRingCat.of (alphaPAlgebra p C c)) n) :
    (cons c rest).toTop =
      CommRingCat.ofHom (algebraMap C (alphaPAlgebra p C c)) ≫ rest.toTop :=
  rfl

/-- **The last ring of a chain of length `n` is free of rank `p ^ n` over the first**, on a basis
indexed by `Fin (p ^ n)`: each stage `R[z]/(z ^ p - c)` is free of rank `p` on the powers of the
adjoined root, and bases multiply along the chain.  For `p = 0` a stage is `R[z]/(1 - c)`, which
is not free of rank `0`, so `p ≠ 0` is asked for. -/
theorem hasFiniteBasis_toTop (hp : p ≠ 0) :
    ∀ {C : CommRingCat.{u}} {n : ℕ} (ch : AlphaPChain p C n),
      HasFiniteBasis ch.toTop.hom (p ^ n)
  | _, _, nil C => by
    rw [pow_zero]
    exact hasFiniteBasis_of_bijective (𝟙 C : C ⟶ C).hom (ConcreteCategory.bijective_of_isIso _)
  | C, _, cons c rest => by
    rw [pow_succ']
    exact hasFiniteBasis_comp (algebraMap C (alphaPAlgebra p C c)) rest.toTop.hom p _
      (hasFiniteBasis_adjoinRoot_X_pow_sub_C C p hp c) (hasFiniteBasis_toTop hp rest)

/-- Over a nontrivial ring the last ring of a chain of length `n` is a free module of rank
`p ^ n` over the first. -/
theorem free_and_rank_toTop (hp : p ≠ 0) {C : CommRingCat.{u}} [Nontrivial C] {n : ℕ}
    (ch : AlphaPChain p C n) :
    letI := ch.toTop.hom.toAlgebra
    Module.Free C ch.top ∧ Module.rank C ch.top = p ^ n := by
  let _ := ch.toTop.hom.toAlgebra
  obtain ⟨b⟩ := hasFiniteBasis_toTop hp ch
  exact ⟨Module.Free.of_basis b, by simpa using rank_eq_card_basis b⟩

end AlphaPChain

/-! ### The normal form of a composition of `α_p`-covers -/

/-- `f : X' ⟶ X` has a **chain normal form**: for every ring `C` identified with `Γ(X, ⊤)` there
are a chain of `α_p`-extensions over `C` and an isomorphism of its last ring with `Γ(X', ⊤)`
under which `f.appTop` becomes the structure map of the chain. -/
def HasAlphaPChainNormalForm (p : ℕ) {X' X : Scheme.{u}} (f : X' ⟶ X) : Prop :=
  ∀ (C : CommRingCat.{u}) (φ : Γ(X, ⊤) ≅ C),
    ∃ (n : ℕ) (ch : AlphaPChain p C n) (e : Γ(X', ⊤) ≅ ch.top),
      f.appTop ≫ e.hom = φ.hom ≫ ch.toTop

/-- **An `α_p`-cover is, on global sections, a single `α_p`-extension** of any ring identified
with the sections of its target.  The identification of the cover with its local model
`Spec(D[z]/(z ^ p - d)) ⟶ Spec(D)` is transported along `D ≅ Γ(X, ⊤) ≅ C`, which carries `d` to
an element `c ∈ C` and `D[z]/(z ^ p - d)` to `C[z]/(z ^ p - c)`. -/
theorem exists_alphaPAlgebra_iso_of_isAlphaPCover {p : ℕ} {Y X : Scheme.{u}} {a : Y ⟶ X}
    (ha : IsAlphaPCover p a) (C : CommRingCat.{u}) (φ : Γ(X, ⊤) ≅ C) :
    ∃ (c : C) (ψ : Γ(Y, ⊤) ≅ CommRingCat.of (alphaPAlgebra p C c)),
      a.appTop ≫ ψ.hom = φ.hom ≫ CommRingCat.ofHom (algebraMap C (alphaPAlgebra p C c)) := by
  obtain ⟨D, hD, -, d, i, j, h⟩ := ha
  let := hD
  let ψ₀ : CommRingCat.of D ⟶ CommRingCat.of (alphaPAlgebra p D d) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk _).comp Polynomial.C)
  let α : CommRingCat.of D ≅ Γ(X, ⊤) := (Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso i.op
  let β : CommRingCat.of (alphaPAlgebra p D d) ≅ Γ(Y, ⊤) :=
    (Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso j.op
  have hαβ : α.hom ≫ a.appTop = ψ₀ ≫ β.hom := by
    have h' := congrArg Scheme.Hom.appTop h
    simp only [Scheme.Hom.comp_appTop] at h'
    unfold alphaPCoverMap at h'
    show ((Scheme.ΓSpecIso _).inv ≫ i.hom.appTop) ≫ a.appTop =
      ψ₀ ≫ ((Scheme.ΓSpecIso _).inv ≫ j.hom.appTop)
    rw [Category.assoc, h', ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have key : a.appTop ≫ β.inv = α.inv ≫ ψ₀ := by
    rw [← cancel_epi α.hom, ← Category.assoc, hαβ]
    simp
  let σ : CommRingCat.of D ≅ C := α ≪≫ φ
  let c : C := σ.hom d
  let τ : AdjoinRoot (Polynomial.X ^ p - Polynomial.C d) ≃+*
      AdjoinRoot (Polynomial.X ^ p - Polynomial.C c) :=
    AdjoinRoot.mapRingEquiv σ.commRingCatIsoToRingEquiv _ _ (Associated.of_eq (by simp [c]; rfl))
  have hτr (r : D) : τ (AdjoinRoot.of _ r) = AdjoinRoot.of _ (σ.hom r) := by
    rw [AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_of]
    rfl
  let τ' : alphaPAlgebra p D d ≃+* alphaPAlgebra p C c := τ
  have hτ : ψ₀ ≫ CommRingCat.ofHom τ'.toRingHom =
      σ.hom ≫ CommRingCat.ofHom (algebraMap C (alphaPAlgebra p C c)) := by
    ext r
    exact hτr r
  refine ⟨c, β.symm ≪≫ τ'.toCommRingCatIso, ?_⟩
  show a.appTop ≫ β.inv ≫ CommRingCat.ofHom τ'.toRingHom = _
  rw [← Category.assoc, key, Category.assoc, hτ]
  simp [σ]

/-- The identity has a chain normal form, with the empty chain. -/
theorem hasAlphaPChainNormalForm_id (p : ℕ) (X : Scheme.{u}) :
    HasAlphaPChainNormalForm p (𝟙 X) := fun C φ =>
  ⟨0, .nil C, φ, by simp⟩

/-- A chain normal form survives postcomposition with an isomorphism: the identification of the
sections of the target is pulled back along it. -/
theorem HasAlphaPChainNormalForm.comp_isIso {p : ℕ} {W X' X : Scheme.{u}} {u : W ⟶ X'}
    (hu : HasAlphaPChainNormalForm p u) (e : X' ⟶ X) [IsIso e] :
    HasAlphaPChainNormalForm p (u ≫ e) := by
  intro C φ
  have : IsIso e.appTop := inferInstanceAs (IsIso (e.app ⊤))
  obtain ⟨n, ch, E, hE⟩ := hu C ((asIso e.appTop).symm ≪≫ φ)
  refine ⟨n, ch, E, ?_⟩
  rw [Scheme.Hom.comp_appTop, Category.assoc, hE, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]

/-- A chain normal form survives postcomposition with an `α_p`-cover: the cover is the first
stage of the new chain, by `exists_alphaPAlgebra_iso_of_isAlphaPCover`. -/
theorem HasAlphaPChainNormalForm.comp_isAlphaPCover {p : ℕ} {W X' X : Scheme.{u}} {u : W ⟶ X'}
    (hu : HasAlphaPChainNormalForm p u) {a : X' ⟶ X} (ha : IsAlphaPCover p a) :
    HasAlphaPChainNormalForm p (u ≫ a) := by
  intro C φ
  obtain ⟨c, ψ, hψ⟩ := exists_alphaPAlgebra_iso_of_isAlphaPCover ha C φ
  obtain ⟨n, rest, E, hE⟩ := hu _ ψ
  refine ⟨n + 1, .cons c rest, E, ?_⟩
  show a.appTop ≫ u.appTop ≫ (E.hom : Γ(W, ⊤) ⟶ rest.top) =
    φ.hom ≫ CommRingCat.ofHom (algebraMap C (alphaPAlgebra p C c)) ≫ rest.toTop
  rw [hE, ← Category.assoc, hψ, Category.assoc]

/-- **A composition of `α_p`-covers has a chain normal form.**  Postcomposing with the
composition preserves chain normal forms, by induction along it; the identity of the source has
the empty chain. -/
theorem hasAlphaPChainNormalForm_of_isAlphaPCoverComposite {p : ℕ} {X' X : Scheme.{u}}
    {f : X' ⟶ X} (hf : IsAlphaPCoverComposite p f) : HasAlphaPChainNormalForm p f := by
  suffices H : ∀ {W : Scheme.{u}} (u : W ⟶ X'), HasAlphaPChainNormalForm p u →
      HasAlphaPChainNormalForm p (u ≫ f) by
    simpa using H (𝟙 X') (hasAlphaPChainNormalForm_id p X')
  induction hf with
  | of_isIso e he =>
    intro W u hu
    exact hu.comp_isIso e
  | comp hg hh ih =>
    intro W u hu
    simpa only [Category.assoc] using ih _ (hu.comp_isAlphaPCover hg)

/-- **The chain normal form of a composition of `α_p`-covers over its own sections.**  For
`f : X' ⟶ X` a composition of `α_p`-covers there are a chain over `Γ(X, ⊤)` and an isomorphism of
`Γ(X', ⊤)` with its last ring under which `f.appTop` is the structure map of the chain.  (When `X`
is affine so is `X'`, by `isAffine_source_of_isAlphaPCoverComposite`.) -/
theorem exists_alphaPChain_of_isAlphaPCoverComposite {p : ℕ} {X' X : Scheme.{u}}
    {f : X' ⟶ X} (hf : IsAlphaPCoverComposite p f) :
    ∃ (n : ℕ) (ch : AlphaPChain p Γ(X, ⊤) n) (e : Γ(X', ⊤) ≅ ch.top),
      f.appTop ≫ e.hom = ch.toTop := by
  simpa using hasAlphaPChainNormalForm_of_isAlphaPCoverComposite hf Γ(X, ⊤) (Iso.refl _)

/-- A ring map identified with the structure map of a chain of length `n` is free of rank
`p ^ n`. -/
theorem AlphaPChain.hasFiniteBasis_of_iso {p : ℕ} (hp : p ≠ 0) {R S : CommRingCat.{u}}
    (g : R ⟶ S) {n : ℕ} (ch : AlphaPChain p R n) (e : S ≅ ch.top)
    (he : g ≫ e.hom = ch.toTop) : HasFiniteBasis g.hom (p ^ n) := by
  refine _root_.AlgebraicGeometry.hasFiniteBasis_of_iso _ _ (RingEquiv.refl _)
    e.commRingCatIsoToRingEquiv ?_ _ (ch.hasFiniteBasis_toTop hp)
  ext r
  exact congrArg (fun k : R ⟶ ch.top => k r) he

/-- **The spectrum of a chain is a composition of `α_p`-covers**, when `p` vanishes in the first
ring: `Spec(R_n) ⟶ Spec(C)` is the composite of the local models `Spec(R_{i+1}) ⟶ Spec(R_i)`. -/
theorem AlphaPChain.isAlphaPCoverComposite_spec_toTop {p : ℕ} :
    ∀ {C : CommRingCat.{u}} {n : ℕ} (ch : AlphaPChain p C n), (p : C) = 0 →
      IsAlphaPCoverComposite p (Spec.map ch.toTop)
  | _, _, nil C, _ => .of_isIso _ (inferInstanceAs (IsIso (Spec.map (𝟙 C))))
  | C, _, cons c rest, hp => by
    have hp' : (p : alphaPAlgebra p C c) = 0 := by
      simpa using congrArg (algebraMap C (alphaPAlgebra p C c)) hp
    have hα : IsAlphaPCover p (alphaPCoverMap p C c) :=
      ⟨C, inferInstance, hp, c, Iso.refl _, Iso.refl _, by simp⟩
    rw [show Spec.map (cons c rest).toTop = Spec.map rest.toTop ≫ alphaPCoverMap p C c from
      Spec.map_comp _ _]
    exact isAlphaPCoverComposite_comp p (rest.isAlphaPCoverComposite_spec_toTop hp')
      (by simpa using IsAlphaPCoverComposite.comp hα (.of_isIso (𝟙 _) inferInstance))

/-- **Conversely, a chain normal form between affine schemes makes a composition of
`α_p`-covers**, when `p` vanishes on the target: `f` is then identified with the spectrum of the
structure map of the chain. -/
theorem isAlphaPCoverComposite_of_alphaPChain {p : ℕ} {X' X : Scheme.{u}} [IsAffine X]
    [IsAffine X'] {f : X' ⟶ X} (hp : (p : Γ(X, ⊤)) = 0) {n : ℕ} (ch : AlphaPChain p Γ(X, ⊤) n)
    (e : Γ(X', ⊤) ≅ ch.top) (he : f.appTop ≫ e.hom = ch.toTop) :
    IsAlphaPCoverComposite p f := by
  have hsq : f ≫ X.isoSpec.hom = (X'.isoSpec.hom ≫ Spec.map e.inv) ≫ Spec.map ch.toTop := by
    rw [Category.assoc, ← Spec.map_comp, (Iso.comp_inv_eq _).mpr he.symm,
      Scheme.isoSpec_hom_naturality]
  exact isAlphaPCoverComposite_of_iso p f _ (X'.isoSpec ≪≫ Scheme.Spec.mapIso e.symm.op)
    X.isoSpec hsq (ch.isAlphaPCoverComposite_spec_toTop hp)

/-! ### Restriction to smaller opens, and the basis -/

/-- Restricting a morphism to an open `W` of the target is the base change, along the inclusion
`W ⟶ U`, of its restriction to a larger open `U`. -/
theorem isPullback_morphismRestrict_homOfLE {X' X : Scheme.{u}} (f : X' ⟶ X) {W U : X.Opens}
    (hWU : W ≤ U) :
    IsPullback (X'.homOfLE (f.preimage_mono hWU)) (f ∣_ W) (f ∣_ U) (X.homOfLE hWU) := by
  refine IsPullback.of_right ?_ (morphismRestrict_homOfLE f W U hWU).symm
    (isPullback_morphismRestrict f U).flip
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  exact (isPullback_morphismRestrict f W).flip

/-- **A composition of `α_p`-covers over an open `U` restricts to one over every affine open
`W ⊆ U`**: the restriction is a base change along `W ⟶ U`. -/
theorem IsAlphaPCoverComposite.morphismRestrict_of_le {p : ℕ} {X' X : Scheme.{u}}
    {f : X' ⟶ X} {W U : X.Opens} (hWU : W ≤ U) (hW : IsAffineOpen W)
    (hU : IsAlphaPCoverComposite p (f ∣_ U)) : IsAlphaPCoverComposite p (f ∣_ W) :=
  have : IsAffine W := hW
  IsAlphaPCoverComposite.of_isPullback (isPullback_morphismRestrict_homOfLE f hWU) p hU

/-- **Every neighbourhood of every point of the target of an iterated `α_p`-cover contains an
affine open neighbourhood over which the cover is a composition of `α_p`-covers.**  The point has
some neighbourhood `U` over which the cover is such a composition; an affine open inside
`U ∩ N` around the point is one too, by `IsAlphaPCoverComposite.morphismRestrict_of_le`. -/
theorem exists_isAffineOpen_isAlphaPCoverComposite {p : ℕ} {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsIteratedAlphaPCover p f) {x : X} {N : X.Opens} (hx : x ∈ N) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ N ∧ IsAlphaPCoverComposite p (f ∣_ W) := by
  obtain ⟨U, hxU, hU⟩ := hf.2 x
  obtain ⟨W, hW, hxW, hWle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ N from ⟨hxU, hx⟩)
  exact ⟨W, hW, hxW, hWle.trans inf_le_right,
    hU.morphismRestrict_of_le (hWle.trans inf_le_left) hW⟩

/-- **The affine opens over which an iterated `α_p`-cover is a composition of `α_p`-covers form a
basis of the topology of the target.** -/
theorem isBasis_isAlphaPCoverComposite {p : ℕ} {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsIteratedAlphaPCover p f) :
    TopologicalSpace.Opens.IsBasis
      {W : X.Opens | IsAffineOpen W ∧ IsAlphaPCoverComposite p (f ∣_ W)} := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {N x} hx => ?_
  obtain ⟨W, hW, hxW, hWN, hc⟩ := exists_isAffineOpen_isAlphaPCoverComposite hf hx
  exact ⟨W, ⟨hW, hc⟩, hxW, hWN⟩

/-- The sections of a restriction over the whole of its source and target are the sections over
the open set it restricts to. -/
theorem app_comp_topIso_inv {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens) :
    f.app U ≫ (f ⁻¹ᵁ U).topIso.inv = U.topIso.inv ≫ (f ∣_ U).appTop := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The chain normal form over an open of the target.**  If the restriction of `f` to an open
`W` is a composition of `α_p`-covers, there are a chain over `Γ(X, W)` and an isomorphism of
`Γ(X', f ⁻¹ᵁ W)` with its last ring under which `f.app W` is the structure map of the chain. -/
theorem exists_alphaPChain_app_of_isAlphaPCoverComposite {p : ℕ} {X' X : Scheme.{u}}
    {f : X' ⟶ X} {W : X.Opens} (hW : IsAlphaPCoverComposite p (f ∣_ W)) :
    ∃ (n : ℕ) (ch : AlphaPChain p Γ(X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top),
      f.app W ≫ e.hom = ch.toTop := by
  obtain ⟨n, ch, e, he⟩ := hasAlphaPChainNormalForm_of_isAlphaPCoverComposite hW _ W.topIso
  refine ⟨n, ch, (f ⁻¹ᵁ W).topIso.symm ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, app_comp_topIso_inv, Category.assoc, he,
    Iso.inv_hom_id_assoc]

/-- **The chain normal form on a basis.**  Every neighbourhood `N` of every point `x` of the
target of an iterated `α_p`-cover `f` contains an affine open `W ∋ x`, with affine preimage, over
which `f` has a chain normal form: `Γ(X', f ⁻¹ᵁ W)` is, as a `Γ(X, W)`-algebra, the last ring of a
chain of `α_p`-extensions over `Γ(X, W)`. -/
theorem exists_isAffineOpen_alphaPChain {p : ℕ} {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsIteratedAlphaPCover p f) {x : X} {N : X.Opens} (hx : x ∈ N) :
    ∃ W : X.Opens, IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧ x ∈ W ∧ W ≤ N ∧
      ∃ (n : ℕ) (ch : AlphaPChain p Γ(X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top),
        f.app W ≫ e.hom = ch.toTop := by
  obtain ⟨W, hW, hxW, hWN, hc⟩ := exists_isAffineOpen_isAlphaPCoverComposite hf hx
  have : IsAffine W := hW
  exact ⟨W, hW, isAffine_source_of_isAlphaPCoverComposite p hc, hxW, hWN,
    exists_alphaPChain_app_of_isAlphaPCoverComposite hc⟩

/-! ### The degree -/

/-- **An iterated `α_p`-cover is an affine morphism**: every point of the target has an affine
open neighbourhood with affine preimage, by `exists_isAffineOpen_alphaPChain`. -/
theorem isAffineHom_of_isIteratedAlphaPCover {p : ℕ} {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsIteratedAlphaPCover p f) : IsAffineHom f :=
  isAffineHom_of_forall_exists_isAffineOpen f fun _ =>
    let ⟨W, hW, hW', hxW, _⟩ := exists_isAffineOpen_alphaPChain hf (N := ⊤) trivial
    ⟨W, hxW, hW, hW'⟩

/-- A basis of the sections over an open set is a basis of the sections of the restriction over
the whole of its source and target; the converse of `hasFiniteBasis_app_of_morphismRestrict`. -/
theorem hasFiniteBasis_morphismRestrict_of_app {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    (n : ℕ) (h : HasFiniteBasis (f.app U).hom n) : HasFiniteBasis (f ∣_ U).appTop.hom n := by
  apply hasFiniteBasis_of_iso _ _ U.topIso.commRingCatIsoToRingEquiv
    (f ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv ?_ n h
  apply CommRingCat.hom_ext_iff.mp
  show (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ f.app U
  rw [← cancel_epi U.topIso.inv, ← Category.assoc, ← app_comp_topIso_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- A free module of finite rank `q` over a nontrivial ring has a basis indexed by `Fin q`. -/
theorem nonempty_basis_fin_of_rank_eq {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] {q : ℕ} (h : Module.rank R M = q) :
    Nonempty (Module.Basis (Fin q) R M) := by
  have : Module.Finite R M := Module.rank_lt_aleph0_iff.mp (by simp [h])
  exact ⟨Module.finBasisOfFinrankEq R M (Module.finrank_eq_of_rank_eq h)⟩

/-- **The degree of an affine morphism is locally constant**: if `f` is an affine morphism of
constant degree `q` and the sections of `f` over an affine open `W` containing a point are free
of rank `m` over the sections of `W`, then `q = m`.  Both ranks are computed again over a smaller
affine open `V ∋ x` inside `W` and inside the open `U` that `HasConstantDegree` provides, where
they are ranks of one free module over a nonzero ring. -/
theorem eq_of_hasConstantDegree_of_hasFiniteBasis {X' X : Scheme.{u}} {f : X' ⟶ X}
    [IsAffineHom f] {q : ℕ} (hq : HasConstantDegree f q) {W : X.Opens} (hW : IsAffineOpen W)
    {x : X} (hxW : x ∈ W) {m : ℕ} (hm : HasFiniteBasis (f.app W).hom m) : q = m := by
  obtain ⟨U, hU, hxU, hfree, hrank⟩ := hq x
  obtain ⟨V, hV, hxV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ W from ⟨hxU, hxW⟩)
  have : IsAffine U := hU
  have : IsAffine W := hW
  have : IsAffine V := hV
  have : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  have : IsAffine (f ⁻¹ᵁ W) := hW.preimage f
  have hqU : HasFiniteBasis (f.app U).hom q := by
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    let := (f.app U).hom.toAlgebra
    exact nonempty_basis_fin_of_rank_eq hrank
  have hVq : HasFiniteBasis (f ∣_ V).appTop.hom q :=
    HasFiniteBasis.of_isPullback_appTop
      (isPullback_morphismRestrict_homOfLE f (hVle.trans inf_le_left)) q
      (hasFiniteBasis_morphismRestrict_of_app f U q hqU)
  have hVm : HasFiniteBasis (f ∣_ V).appTop.hom m :=
    HasFiniteBasis.of_isPullback_appTop
      (isPullback_morphismRestrict_homOfLE f (hVle.trans inf_le_right)) m
      (hasFiniteBasis_morphismRestrict_of_app f W m hm)
  have : Nonempty (↑(⊤ : (V : Scheme.{u}).Opens)) := ⟨⟨⟨x, hxV⟩, trivial⟩⟩
  let := (f ∣_ V).appTop.hom.toAlgebra
  obtain ⟨b⟩ := hVq
  obtain ⟨b'⟩ := hVm
  simpa using (rank_eq_card_basis b).symm.trans (rank_eq_card_basis b')

/-- **Over a nonempty affine open with a chain of length `n`, the constant degree of an iterated
`α_p`-cover is `p ^ n`.**  The chain makes the sections over `W` free of rank `p ^ n`, and the
degree is locally constant (`eq_of_hasConstantDegree_of_hasFiniteBasis`), an iterated
`α_p`-cover being an affine morphism. -/
theorem eq_pow_of_hasConstantDegree_of_alphaPChain {p : ℕ} (hp : p ≠ 0) {X' X : Scheme.{u}}
    {f : X' ⟶ X} (hf : IsIteratedAlphaPCover p f) {q : ℕ} (hq : HasConstantDegree f q)
    {W : X.Opens} (hW : IsAffineOpen W) (hne : (W : Set X).Nonempty) {n : ℕ}
    (ch : AlphaPChain p Γ(X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)
    (he : f.app W ≫ e.hom = ch.toTop) : q = p ^ n := by
  have := isAffineHom_of_isIteratedAlphaPCover hf
  obtain ⟨x, hx⟩ := hne
  exact eq_of_hasConstantDegree_of_hasFiniteBasis hq hW hx
    (AlphaPChain.hasFiniteBasis_of_iso hp _ ch e he)

/-- **The local normal form of an iterated `α_p`-cover of constant degree `q`.**  Every
neighbourhood `N` of every point `x` of the target contains an affine open `W ∋ x`, with affine
preimage, over which `Γ(X', f ⁻¹ᵁ W)` is the last ring of a chain of `n` successive
`α_p`-extensions `R_{i+1} = R_i[z]/(z ^ p - c_i)` of `R_0 = Γ(X, W)`, and `q = p ^ n`. -/
theorem exists_alphaPChain_and_eq_pow_of_hasConstantDegree {p : ℕ} (hp : p ≠ 0)
    {X' X : Scheme.{u}} {f : X' ⟶ X} (hf : IsIteratedAlphaPCover p f) {q : ℕ}
    (hq : HasConstantDegree f q) {x : X} {N : X.Opens} (hx : x ∈ N) :
    ∃ W : X.Opens, IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧ x ∈ W ∧ W ≤ N ∧
      ∃ (n : ℕ) (ch : AlphaPChain p Γ(X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top),
        f.app W ≫ e.hom = ch.toTop ∧ q = p ^ n := by
  obtain ⟨W, hW, hW', hxW, hWN, n, ch, e, he⟩ := exists_isAffineOpen_alphaPChain hf hx
  exact ⟨W, hW, hW', hxW, hWN, n, ch, e, he,
    eq_pow_of_hasConstantDegree_of_alphaPChain hp hf hq hW ⟨x, hxW⟩ ch e he⟩

end AlgebraicGeometry

end
