module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology

/-!
# The `μ_n`-torsor of a `ℤ/n`-torsor scheme

Let `S` be a scheme over a field `k` containing a primitive `n`-th root of unity `ζ`, and let
`p : T ⟶ S` be étale and surjective with an action `τ : ℤ/n → End_S(T)` making `T` a `ℤ/n`-torsor
over `S` in the scheme sense: `∐_{a ∈ ℤ/n} T ⟶ T ×_S T`, `(t, a) ↦ (t, τ_a t)`, is an isomorphism.
Then the sheaf of sections `U ↦ Hom_S(U, T)` on the small étale site of `S` is a torsor under
`μ_n`: an `n`-th root of unity `x ∈ Γ(U, 𝒪_U)` decomposes `U` into the open and closed pieces
`U_a = {x = ζ^a}`, and acts on a section `s` by `τ_a ∘ s` on `U_a`.

The pieces are the basic open sets of the Lagrange idempotents `e_a(x)` attached to the `n`
distinct roots `ζ^a` (`Stacks.Kummer.rootIdempotent`), and the action is glued from the `τ_a ∘ s`
along them.

## Main definitions

* `Stacks.Kummer.rootSMul`: the action of an `n`-th root of unity on a morphism into `T`.
* `Stacks.Kummer.schemeTorsor`: the `μ_n`-torsor of sections of `T`.

## Main results

* `Stacks.Kummer.comp_rootSMul_of_eq`: where `x = ζ^a`, `x • s = τ_a ∘ s`.
* `Stacks.Kummer.exists_rootSMul_eq`, `Stacks.Kummer.rootSMul_injective`: simple transitivity.
* `Stacks.Kummer.exists_hom_of_schemeTorsor_eq`: torsor schemes with the same `μ_n`-torsor class
  are related by an equivariant morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Polynomial

universe u

namespace Stacks.Kummer

section Pieces

variable {k : Type u} [Field k] [DecidableEq k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) {n : ℕ}
  [NeZero n] (ζ : k)

/-- The structure map `k → Γ(W, 𝒪_W)` of a scheme `W` over `S`. -/
def baseRingMap {W : Scheme.{u}} (g : W ⟶ S) : k →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ g.appTop).hom

omit [DecidableEq k] in
/-- The structure maps are compatible with composition. -/
theorem baseRingMap_comp {V W : Scheme.{u}} (h : V ⟶ W) (g : W ⟶ S) :
    h.appTop.hom.comp (baseRingMap f g) = baseRingMap f (h ≫ g) := by
  rw [baseRingMap, baseRingMap, ← CommRingCat.hom_comp, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]

omit [DecidableEq k] in
/-- The structure maps are compatible with composition, elementwise. -/
theorem baseRingMap_comp_apply {V W : Scheme.{u}} (h : V ⟶ W) (g : W ⟶ S) (c : k) :
    h.appTop.hom (baseRingMap f g c) = baseRingMap f (h ≫ g) c := by
  rw [← baseRingMap_comp f h g]
  rfl

/-- The Lagrange idempotent of `x ∈ Γ(W, 𝒪_W)` at the root of unity `ζ ^ a`. -/
def pieceIdem {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (a : ZMod n) : Γ(W, ⊤) :=
  (Lagrange.basis (nthRootsFinset n (1 : k)) id (ζ ^ a.val)).eval₂ (baseRingMap f g) x

omit [NeZero n] in
/-- The Lagrange idempotents are compatible with pullback along a morphism. -/
theorem pieceIdem_comp {V W : Scheme.{u}} (h : V ⟶ W) (g : W ⟶ S) (x : Γ(W, ⊤)) (a : ZMod n) :
    h.appTop.hom (pieceIdem f ζ g x a) = pieceIdem f ζ (h ≫ g) (h.appTop.hom x) a := by
  rw [pieceIdem, pieceIdem, hom_eval₂, baseRingMap_comp]

/-- The open piece `{x = ζ ^ a}` of `W`. -/
abbrev piece {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (a : ZMod n) : W.Opens :=
  W.basicOpen (pieceIdem f ζ g x a)

variable {ζ} (hζ : IsPrimitiveRoot ζ n)
include hζ

omit [DecidableEq k] in
/-- `ζ ^ a` is an `n`-th root of unity. -/
theorem pow_val_mem_nthRootsFinset (a : ZMod n) : ζ ^ a.val ∈ nthRootsFinset n (1 : k) := by
  rw [mem_nthRootsFinset (Nat.pos_of_ne_zero (NeZero.ne n)), ← pow_mul, mul_comm, pow_mul,
    hζ.pow_eq_one, one_pow]

omit [DecidableEq k] in
/-- `a ↦ ζ ^ a` is injective on `ℤ/n`. -/
theorem pow_val_injective : Function.Injective fun a : ZMod n => ζ ^ a.val :=
  fun a b h => ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

/-- The `n`-th roots of unity in `k` are the powers `ζ ^ a`, `a ∈ ℤ/n`. -/
theorem nthRootsFinset_eq_image :
    nthRootsFinset n (1 : k) = Finset.univ.image fun a : ZMod n => ζ ^ a.val := by
  symm
  refine Finset.eq_of_subset_of_card_le (fun ρ hρ => ?_) ?_
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hρ
    exact pow_val_mem_nthRootsFinset hζ a
  · rw [Finset.card_image_of_injective _ (pow_val_injective hζ), Finset.card_univ, ZMod.card,
      hζ.card_nthRootsFinset]

omit [DecidableEq k] in
/-- `ζ ^ (a + b) = ζ ^ a * ζ ^ b` for `a b : ℤ/n`. -/
theorem pow_val_add (a b : ZMod n) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add, ← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul,
    hζ.pow_eq_one, one_pow, mul_one, Nat.mod_add_div]

/-- The Lagrange idempotents sum to one. -/
theorem sum_pieceIdem {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) :
    ∑ a : ZMod n, pieceIdem f ζ g x a = 1 := by
  have h1 := Lagrange.sum_basis (s := nthRootsFinset n (1 : k)) (v := id) (Set.injOn_id _)
    ⟨1, (mem_nthRootsFinset (Nat.pos_of_ne_zero (NeZero.ne n)) (1 : k)).2 (one_pow n)⟩
  have h2 := congrArg (fun P : k[X] => P.eval₂ (baseRingMap f g) x) h1
  simp only [eval₂_finsetSum, eval₂_one] at h2
  set F : k → Γ(W, ⊤) := fun j =>
    (Lagrange.basis (nthRootsFinset n (1 : k)) id j).eval₂ (baseRingMap f g) x with hF
  have h3 : ∑ j ∈ nthRootsFinset n (1 : k), F j = ∑ a : ZMod n, F (ζ ^ a.val) := by
    rw [nthRootsFinset_eq_image hζ, Finset.sum_image fun a _ b _ h => pow_val_injective hζ h]
  exact h3 ▸ h2

/-- If `x ^ n = 1`, then `(x - ζ ^ a) e_a(x) = 0`. -/
theorem sub_mul_pieceIdem {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (a : ZMod n) : (x - baseRingMap f g (ζ ^ a.val)) * pieceIdem f ζ g x a = 0 := by
  classical
  let : Algebra k Γ(W, ⊤) := (baseRingMap f g).toAlgebra
  have := sub_mul_rootIdempotent hζ (NeZero.ne n) x hx (pow_val_mem_nthRootsFinset hζ a)
  simp only [rootIdempotent, aeval_def, RingHom.algebraMap_toAlgebra] at this
  exact this

/-- If `x ^ n = 1`, the Lagrange idempotents at distinct roots are orthogonal. -/
theorem pieceIdem_mul_pieceIdem {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    {a b : ZMod n} (hab : a ≠ b) : pieceIdem f ζ g x a * pieceIdem f ζ g x b = 0 := by
  have ha := sub_mul_pieceIdem f hζ g x hx a
  have hb := sub_mul_pieceIdem f hζ g x hx b
  have hne : ζ ^ a.val - ζ ^ b.val ≠ 0 := sub_ne_zero.2 fun h => hab (pow_val_injective hζ h)
  have hunit : IsUnit (baseRingMap f g (ζ ^ a.val - ζ ^ b.val)) := (Ne.isUnit hne).map _
  refine (hunit.mul_right_eq_zero).1 ?_
  rw [map_sub]
  linear_combination (pieceIdem f ζ g x a) * hb - (pieceIdem f ζ g x b) * ha

/-- The Lagrange idempotent `e_a` at the constant `ζ ^ b` is `1` if `a = b` and `0` otherwise. -/
theorem pieceIdem_baseRingMap {W : Scheme.{u}} (g : W ⟶ S) (a b : ZMod n) :
    pieceIdem f ζ g (baseRingMap f g (ζ ^ b.val)) a = if a = b then 1 else 0 := by
  rw [pieceIdem, eval₂_at_apply]
  split_ifs with h
  · subst h
    have := Lagrange.eval_basis_self (s := nthRootsFinset n (1 : k)) (v := id) (Set.injOn_id _)
      (pow_val_mem_nthRootsFinset hζ a)
    simp only [id] at this ⊢
    rw [this, map_one]
  · have := Lagrange.eval_basis_of_ne (s := nthRootsFinset n (1 : k)) (v := id)
      (fun h' => h (pow_val_injective hζ h')) (pow_val_mem_nthRootsFinset hζ b)
    simp only [id] at this ⊢
    rw [this, map_zero]

/-- The pieces `{x = ζ ^ a}` cover `W`. -/
theorem isOpenCover_piece {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) :
    TopologicalSpace.IsOpenCover (fun a : ZMod n => piece f ζ g x a) := by
  have hspan : Ideal.span (Set.range (pieceIdem f ζ g x : ZMod n → Γ(W, ⊤))) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← sum_pieceIdem f hζ g x]
    exact Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨a, rfl⟩
  have h := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := W) ⊤ _ hspan
  rwa [iSup_range] at h

/-- If `x ^ n = 1`, distinct pieces are disjoint. -/
theorem piece_inf_piece {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    {a b : ZMod n} (hab : a ≠ b) : piece f ζ g x a ⊓ piece f ζ g x b = ⊥ := by
  rw [← Scheme.basicOpen_mul, pieceIdem_mul_pieceIdem f hζ g x hx hab, Scheme.basicOpen_zero]

/-- On the piece `{x = ζ ^ a}`, `x` restricts to `ζ ^ a`. -/
theorem appTop_ι_piece {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (a : ZMod n) : (piece f ζ g x a).ι.appTop.hom x =
      baseRingMap f ((piece f ζ g x a).ι ≫ g) (ζ ^ a.val) := by
  have hunit := isUnit_ι_appTop_basicOpen W (pieceIdem f ζ g x a)
  have himg := congrArg (piece f ζ g x a).ι.appTop.hom (sub_mul_pieceIdem f hζ g x hx a)
  rw [map_mul, map_zero, map_sub, baseRingMap_comp_apply] at himg
  exact sub_eq_zero.1 (hunit.mul_left_eq_zero.1 himg)

/-- If `x` pulls back to `ζ ^ a` along `h`, the preimage of the piece `{x = ζ ^ a}` is
everything. -/
theorem preimage_piece_eq_top {V W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (h : V ⟶ W)
    (a : ZMod n) (hxa : h.appTop.hom x = baseRingMap f (h ≫ g) (ζ ^ a.val)) :
    h ⁻¹ᵁ piece f ζ g x a = ⊤ := by
  rw [Scheme.preimage_basicOpen_top, pieceIdem_comp, hxa, pieceIdem_baseRingMap f hζ,
    ite_eq_left rfl, Scheme.basicOpen_one]

/-- If `x` pulls back to `ζ ^ a` along `h`, then `h` factors through the piece `{x = ζ ^ a}`. -/
theorem range_subset_piece {V W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (h : V ⟶ W)
    (a : ZMod n) (hxa : h.appTop.hom x = baseRingMap f (h ≫ g) (ζ ^ a.val)) :
    Set.range h ⊆ Set.range (piece f ζ g x a).ι := by
  rintro _ ⟨v, rfl⟩
  rw [Scheme.Opens.range_ι]
  have : v ∈ h ⁻¹ᵁ piece f ζ g x a := by
    rw [preimage_piece_eq_top f hζ g x h a hxa]; trivial
  exact this

/-- If `h` factors through the piece `{x = ζ ^ a}`, then `x` pulls back to `ζ ^ a` along `h`. -/
theorem appTop_eq_of_range_subset {V W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (h : V ⟶ W) (a : ZMod n) (H : Set.range h ⊆ Set.range (piece f ζ g x a).ι) :
    h.appTop.hom x = baseRingMap f (h ≫ g) (ζ ^ a.val) := by
  rw [← IsOpenImmersion.lift_fac _ _ H, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply, appTop_ι_piece f hζ g x hx a, baseRingMap_comp_apply, Category.assoc]

/-- The pieces `{x = ζ ^ a} ⊓ {y = ζ ^ b}` cover `W`. -/
private theorem isOpenCover_piece_inf_piece {W : Scheme.{u}} (g : W ⟶ S) (x y : Γ(W, ⊤)) :
    TopologicalSpace.IsOpenCover (fun ab : ZMod n × ZMod n =>
      piece f ζ g x ab.1 ⊓ piece f ζ g y ab.2) := by
  change (⨆ ab : ZMod n × ZMod n, _) = ⊤
  rw [← iSup_inf_iSup, isOpenCover_piece f hζ g, isOpenCover_piece f hζ g, top_inf_eq]

/-- On `{x = ζ ^ a} ⊓ {y = ζ ^ b}`, `x` restricts to `ζ ^ a` and `y` to `ζ ^ b`. -/
private theorem appTop_ι_piece_inf_piece {W : Scheme.{u}} (g : W ⟶ S) (x y : Γ(W, ⊤))
    (hx : x ^ n = 1) (hy : y ^ n = 1) (a b : ZMod n) :
    (piece f ζ g x a ⊓ piece f ζ g y b).ι.appTop.hom x =
        baseRingMap f ((piece f ζ g x a ⊓ piece f ζ g y b).ι ≫ g) (ζ ^ a.val) ∧
      (piece f ζ g x a ⊓ piece f ζ g y b).ι.appTop.hom y =
        baseRingMap f ((piece f ζ g x a ⊓ piece f ζ g y b).ι ≫ g) (ζ ^ b.val) :=
  ⟨appTop_eq_of_range_subset f hζ g x hx _ a
      (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact inf_le_left),
    appTop_eq_of_range_subset f hζ g y hy _ b
      (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact inf_le_right)⟩

end Pieces

section Action

variable {k : Type u} [Field k] [DecidableEq k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) {n : ℕ}
  [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) {T : Scheme.{u}} (τ : ZMod n → (T ⟶ T))

/-- The open cover of `W` by the pieces `{x = ζ ^ a}`. -/
def pieceCover {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) : W.OpenCover :=
  W.openCoverOfIsOpenCover (fun a : ZMod n => piece f ζ g x a) (isOpenCover_piece f hζ g x)

/-- The members of `pieceCover` are the inclusions of the pieces. -/
theorem pieceCover_f {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (a : ZMod n) :
    (pieceCover f hζ g x).f a = (piece f ζ g x a).ι := rfl

/-- Morphisms restricted to opens agree on overlaps if distinct opens have empty overlap. -/
private theorem pullback_ι_comp_eq_of_isEmpty {W Z : Scheme.{u}} {J : Type*} (O : J → W.Opens)
    (ψ : J → (W ⟶ Z)) (hO : ∀ a b, a ≠ b → IsEmpty ↑(pullback (O a).ι (O b).ι)) (a b : J) :
    pullback.fst (O a).ι (O b).ι ≫ ((O a).ι ≫ ψ a) =
      pullback.snd (O a).ι (O b).ι ≫ ((O b).ι ≫ ψ b) := by
  by_cases hab : a = b
  · subst hab
    exact pullback.condition_assoc _
  · exact (@isInitialOfIsEmpty _ (hO a b hab)).hom_ext _ _

/-- The morphisms `τ_a ∘ s` on the pieces agree on overlaps. -/
theorem pieceCover_compat {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (s : W ⟶ T) (a b : ZMod n) :
    pullback.fst ((pieceCover f hζ g x).f a) ((pieceCover f hζ g x).f b) ≫
        ((piece f ζ g x a).ι ≫ s ≫ τ a) =
      pullback.snd ((pieceCover f hζ g x).f a) ((pieceCover f hζ g x).f b) ≫
        ((piece f ζ g x b).ι ≫ s ≫ τ b) := by
  simp only [pieceCover_f]
  refine pullback_ι_comp_eq_of_isEmpty (fun a => piece f ζ g x a) (fun a => s ≫ τ a)
    (fun a b hab => ⟨fun q => ?_⟩) a b
  have hq : (piece f ζ g x a).ι (pullback.fst (piece f ζ g x a).ι (piece f ζ g x b).ι q) =
      (piece f ζ g x b).ι (pullback.snd (piece f ζ g x a).ι (piece f ζ g x b).ι q) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have ha : (piece f ζ g x a).ι (pullback.fst (piece f ζ g x a).ι (piece f ζ g x b).ι q) ∈
      piece f ζ g x a := (pullback.fst (piece f ζ g x a).ι (piece f ζ g x b).ι q).2
  have hb : (piece f ζ g x b).ι (pullback.snd (piece f ζ g x a).ι (piece f ζ g x b).ι q) ∈
      piece f ζ g x b := (pullback.snd (piece f ζ g x a).ι (piece f ζ g x b).ι q).2
  have : _ ∈ piece f ζ g x a ⊓ piece f ζ g x b := ⟨ha, hq ▸ hb⟩
  rw [piece_inf_piece f hζ g x hx hab] at this
  exact this

include hζ in
/-- Morphisms out of `W` that agree on every piece are equal. -/
theorem piece_hom_ext {W Z : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (φ ψ : W ⟶ Z)
    (h : ∀ a : ZMod n, (piece f ζ g x a).ι ≫ φ = (piece f ζ g x a).ι ≫ ψ) : φ = ψ :=
  (pieceCover f hζ g x).hom_ext φ ψ h

/-- **The action of an `n`-th root of unity `x` on a morphism `s : W ⟶ T`**: `τ_a ∘ s` on the
piece `{x = ζ ^ a}`. -/
def rootSMul {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1) (s : W ⟶ T) : W ⟶ T :=
  (pieceCover f hζ g x).glueMorphisms (fun a => (piece f ζ g x a).ι ≫ s ≫ τ a)
    (pieceCover_compat f hζ τ g x hx s)

/-- On the piece `{x = ζ ^ a}`, `x • s` is `τ_a ∘ s`. -/
@[reassoc]
theorem ι_rootSMul {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1) (s : W ⟶ T)
    (a : ZMod n) :
    (piece f ζ g x a).ι ≫ rootSMul f hζ τ g x hx s = (piece f ζ g x a).ι ≫ s ≫ τ a :=
  (pieceCover f hζ g x).ι_glueMorphisms (fun a => (piece f ζ g x a).ι ≫ s ≫ τ a)
    (pieceCover_compat f hζ τ g x hx s) a

/-- **Where `x = ζ ^ a`, `x • s = τ_a ∘ s`.** -/
theorem comp_rootSMul_of_eq {V W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (s : W ⟶ T) (h : V ⟶ W) (a : ZMod n)
    (hxa : h.appTop.hom x = baseRingMap f (h ≫ g) (ζ ^ a.val)) :
    h ≫ rootSMul f hζ τ g x hx s = h ≫ s ≫ τ a := by
  have H := range_subset_piece f hζ g x h a hxa
  rw [← IsOpenImmersion.lift_fac _ _ H, Category.assoc, ι_rootSMul, Category.assoc]

/-- If `τ` preserves `p`, then `x • s` lies over the same morphism to `S` as `s`. -/
theorem rootSMul_comp {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    {p : T ⟶ S} (hτp : ∀ a, τ a ≫ p = p) (s : W ⟶ T) (hs : s ≫ p = g) :
    rootSMul f hζ τ g x hx s ≫ p = g := by
  refine piece_hom_ext f hζ g x _ _ fun a => ?_
  rw [ι_rootSMul_assoc, hτp, hs]

/-- The comparison `∐_{a ∈ ℤ/n} T ⟶ T ×_S T`, `(t, a) ↦ (t, τ_a t)`. -/
def torsorComparison {p : T ⟶ S} (hτp : ∀ a, τ a ≫ p = p) :
    (∐ fun _ : ZMod n => T) ⟶ pullback p p :=
  Sigma.desc fun a => pullback.lift (𝟙 T) (τ a) (by rw [Category.id_comp, hτp a])

omit [NeZero n] in
/-- The comparison map on the summand `a` is `(id, τ_a)`. -/
theorem ι_torsorComparison {p : T ⟶ S} (hτp : ∀ a, τ a ≫ p = p) (a : ZMod n) :
    Sigma.ι (fun _ : ZMod n => T) a ≫ torsorComparison τ hτp =
      pullback.lift (𝟙 T) (τ a) (by rw [Category.id_comp, hτp a]) :=
  Sigma.ι_comp_desc _ _

omit [NeZero n] in
/-- In a `ℤ/n`-torsor, `τ_a ∘ s = τ_b ∘ s` forces `a = b` unless the source is empty. -/
theorem isEmpty_of_comp_τ_eq {p : T ⟶ S} (hτp : ∀ a, τ a ≫ p = p)
    (hΦ : IsIso (torsorComparison τ hτp)) {V : Scheme.{u}} (s : V ⟶ T) {a b : ZMod n}
    (hab : a ≠ b) (h : s ≫ τ a = s ≫ τ b) : IsEmpty V := by
  have : (s ≫ Sigma.ι (fun _ : ZMod n => T) a) ≫ torsorComparison τ hτp =
      (s ≫ Sigma.ι (fun _ : ZMod n => T) b) ≫ torsorComparison τ hτp := by
    rw [Category.assoc, Category.assoc, ι_torsorComparison, ι_torsorComparison]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, h]
  exact isEmpty_of_commSq_sigmaι_of_ne ⟨(cancel_mono _).1 this⟩ hab

/-- The translations act freely: `τ_a ∘ s = τ_b ∘ s` with `a ≠ b` forces the source to be
empty. -/
def IsFreeTranslation : Prop :=
  ∀ ⦃V : Scheme.{u}⦄ (s : V ⟶ T) ⦃a b : ZMod n⦄, a ≠ b → s ≫ τ a = s ≫ τ b → IsEmpty V

/-- The translations act locally transitively on the fibres of `p`: two morphisms into `T` with
the same image in `S` differ by `τ_a` on the pieces of an open cover. -/
def IsLocallyTransitive (p : T ⟶ S) : Prop :=
  ∀ ⦃W : Scheme.{u}⦄ (s t : W ⟶ T), s ≫ p = t ≫ p → ∃ O : ZMod n → W.Opens,
    TopologicalSpace.IsOpenCover O ∧ ∀ a, (O a).ι ≫ t = (O a).ι ≫ s ≫ τ a

omit [NeZero n] in
/-- The translations of a `ℤ/n`-torsor scheme act freely. -/
theorem isFreeTranslation_of_isIso {p : T ⟶ S} (hτp : ∀ a, τ a ≫ p = p)
    (hΦ : IsIso (torsorComparison τ hτp)) : IsFreeTranslation τ :=
  fun _ s _ _ hab h => isEmpty_of_comp_τ_eq τ hτp hΦ s hab h

omit [NeZero n] in
/-- The translations of a `ℤ/n`-torsor scheme act locally transitively. -/
theorem isLocallyTransitive_of_isIso {p : T ⟶ S} (hτp : ∀ a, τ a ≫ p = p)
    (hΦ : IsIso (torsorComparison τ hτp)) : IsLocallyTransitive τ p := by
  intro W s t hst
  set hmap := pullback.lift s t hst ≫ inv (torsorComparison τ hτp)
  have hcov : TopologicalSpace.IsOpenCover
      (fun a : ZMod n => hmap ⁻¹ᵁ (Sigma.ι (fun _ : ZMod n => T) a).opensRange) := by
    refine top_le_iff.1 fun w _ => ?_
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun _ : ZMod n => T)).exists_eq (hmap w)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hy⟩⟩
  refine ⟨_, hcov, fun a => ?_⟩
  set O := hmap ⁻¹ᵁ (Sigma.ι (fun _ : ZMod n => T) a).opensRange
  have hrange : Set.range (O.ι ≫ hmap) ⊆ Set.range (Sigma.ι (fun _ : ZMod n => T) a) := by
    rintro _ ⟨o, rfl⟩
    have h0 : O.ι o ∈ O := by
      have := Set.mem_range_self (f := O.ι) o
      rwa [Scheme.Opens.range_ι] at this
    rwa [Scheme.Hom.comp_apply]
  set l := IsOpenImmersion.lift (Sigma.ι (fun _ : ZMod n => T) a) (O.ι ≫ hmap) hrange
  have hl : l ≫ Sigma.ι (fun _ : ZMod n => T) a = O.ι ≫ hmap := IsOpenImmersion.lift_fac _ _ _
  have hst' : O.ι ≫ pullback.lift s t hst =
      l ≫ pullback.lift (𝟙 T) (τ a) (by rw [Category.id_comp, hτp a]) := by
    rw [← ι_torsorComparison τ hτp a, ← Category.assoc, hl, Category.assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  have hs' : O.ι ≫ s = l := by
    simpa only [Category.assoc, pullback.lift_fst, Category.comp_id] using
      congrArg (· ≫ pullback.fst p p) hst'
  have ht' : O.ι ≫ t = l ≫ τ a := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd p p) hst'
  rw [ht', ← hs', Category.assoc]

end Action

section BaseChange

variable {S S' T : Scheme.{u}} {n : ℕ} (p : T ⟶ S) (g : S' ⟶ S) (τ : ZMod n → (T ⟶ T))
  (hτp : ∀ a, τ a ≫ p = p)

/-- The translations of the base change `T ×_S S'`. -/
def baseChangeTranslation (a : ZMod n) : pullback p g ⟶ pullback p g :=
  pullback.map p g p g (τ a) (𝟙 S') (𝟙 S) (by rw [Category.comp_id, hτp a]) (by simp)

/-- The translations of the base change lie over the translations of `T`. -/
@[reassoc (attr := simp)]
theorem baseChangeTranslation_fst (a : ZMod n) :
    baseChangeTranslation p g τ hτp a ≫ pullback.fst p g = pullback.fst p g ≫ τ a :=
  pullback.lift_fst _ _ _

/-- The translations of the base change lie over `S'`. -/
@[reassoc (attr := simp)]
theorem baseChangeTranslation_snd (a : ZMod n) :
    baseChangeTranslation p g τ hτp a ≫ pullback.snd p g = pullback.snd p g := by
  rw [baseChangeTranslation, pullback.lift_snd, Category.comp_id]

/-- The translation by `0` of the base change is the identity. -/
theorem baseChangeTranslation_zero (hτ0 : τ 0 = 𝟙 T) :
    baseChangeTranslation p g τ hτp 0 = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [hτ0]

/-- The translations of the base change are additive. -/
theorem baseChangeTranslation_add (hτadd : ∀ a b, τ (a + b) = τ a ≫ τ b) (a b : ZMod n) :
    baseChangeTranslation p g τ hτp (a + b) =
      baseChangeTranslation p g τ hτp a ≫ baseChangeTranslation p g τ hτp b := by
  apply pullback.hom_ext <;> simp [hτadd]

/-- Freeness of the translations is stable under base change. -/
theorem isFreeTranslation_baseChange (h : IsFreeTranslation τ) :
    IsFreeTranslation (baseChangeTranslation p g τ hτp) := by
  intro V s a b hab hs
  refine h (s ≫ pullback.fst p g) hab ?_
  simpa using congrArg (· ≫ pullback.fst p g) hs

/-- Local transitivity of the translations is stable under base change. -/
theorem isLocallyTransitive_baseChange (h : IsLocallyTransitive τ p) :
    IsLocallyTransitive (baseChangeTranslation p g τ hτp) (pullback.snd p g) := by
  intro W s t hst
  obtain ⟨O, hO, hOa⟩ := h (s ≫ pullback.fst p g) (t ≫ pullback.fst p g) (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hst])
  refine ⟨O, hO, fun a => ?_⟩
  apply pullback.hom_ext
  · simpa using hOa a
  · simp only [Category.assoc, baseChangeTranslation_snd]
    exact congrArg ((O a).ι ≫ ·) hst.symm

end BaseChange

section Transitivity

variable {k : Type u} [Field k] [DecidableEq k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) {n : ℕ}
  [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) {T : Scheme.{u}} (τ : ZMod n → (T ⟶ T))

include f hζ in
omit [DecidableEq k] in
/-- If `k` has a primitive `n`-th root of unity, then `n` is invertible on `S`. -/
theorem isUnit_natCast_of_isPrimitiveRoot : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
  have := hζ.neZero'
  have := (isUnit_iff_ne_zero.2 (NeZero.ne ((n : ℕ) : k))).map (baseRingMap f (𝟙 S))
  rwa [map_natCast] at this

omit [NeZero n] in
/-- The underlying function of an `n`-th root of unity has `n`-th power one. -/
theorem coe_pow_eq_one {W : Scheme.{u}} {x : Γ(W, ⊤)ˣ} (hx : x ^ n = 1) :
    (x : Γ(W, ⊤)) ^ n = 1 := by
  rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]

include f hζ in
omit [DecidableEq k] in
/-- `n`-th roots of unity of `Γ(W, 𝒪_W)` are determined on an open cover. -/
theorem eq_of_forall_appTop_eq {W : Scheme.{u}} (g : W ⟶ S) (𝒰 : W.OpenCover)
    (x y : Γ(W, ⊤)ˣ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : ∀ i, (𝒰.f i).appTop.hom (x : Γ(W, ⊤)) = (𝒰.f i).appTop.hom (y : Γ(W, ⊤))) :
    x = y := by
  set E := rootsOfUnityEtaleOverHomEquiv S n (isUnit_natCast_of_isPrimitiveRoot f hζ)
  set mx := (E (Over.mk g)).symm ⟨x, hx⟩
  set my := (E (Over.mk g)).symm ⟨y, hy⟩
  have key : ∀ i, 𝒰.f i ≫ mx.left = 𝒰.f i ≫ my.left := by
    intro i
    let j : Over.mk (𝒰.f i ≫ g) ⟶ Over.mk g := Over.homMk (𝒰.f i) rfl
    have h1 : j ≫ mx = j ≫ my := by
      refine (E _).injective (Subtype.ext ?_)
      rw [rootsOfUnityEtaleOverHomEquiv_naturality, rootsOfUnityEtaleOverHomEquiv_naturality,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact Units.ext (h i)
    exact congrArg CommaMorphism.left h1
  have h2 : mx = my := Over.OverMorphism.ext (𝒰.hom_ext _ _ key)
  exact congrArg Subtype.val ((E (Over.mk g)).symm.injective h2)

/-- `ζ ^ a` as a unit of `Γ(W, 𝒪_W)`. -/
def constRoot {W : Scheme.{u}} (g : W ⟶ S) (a : ZMod n) : Γ(W, ⊤)ˣ :=
  Units.map (baseRingMap f g).toMonoidHom
    (Units.mk0 (ζ ^ a.val) (pow_ne_zero _ (hζ.ne_zero (NeZero.ne n))))

omit [DecidableEq k] in
/-- The underlying function of `constRoot` is the image of `ζ ^ a`. -/
theorem coe_constRoot {W : Scheme.{u}} (g : W ⟶ S) (a : ZMod n) :
    (constRoot f hζ g a : Γ(W, ⊤)) = baseRingMap f g (ζ ^ a.val) := rfl

omit [DecidableEq k] in
/-- `constRoot` is an `n`-th root of unity. -/
theorem constRoot_pow {W : Scheme.{u}} (g : W ⟶ S) (a : ZMod n) : constRoot f hζ g a ^ n = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_constRoot, ← map_pow, ← pow_mul, mul_comm, pow_mul,
    hζ.pow_eq_one, one_pow, map_one, Units.val_one]

/-- The section `ζ ^ a` of the scheme of `n`-th roots of unity over `S`. -/
def constRootSection (a : ZMod n) :
    Over.mk (𝟙 S) ⟶ rootsOfUnityEtaleOver S n (isUnit_natCast_of_isPrimitiveRoot f hζ) :=
  (rootsOfUnityEtaleOverHomEquiv S n (isUnit_natCast_of_isPrimitiveRoot f hζ)
    (Over.mk (𝟙 S))).symm ⟨constRoot f hζ (𝟙 S) a, constRoot_pow f hζ (𝟙 S) a⟩

/-- **Existence in the simple transitivity**: two morphisms into a `ℤ/n`-torsor differ by an
`n`-th root of unity. -/
theorem exists_rootSMul_eq {p : T ⟶ S} (hfree : IsFreeTranslation τ)
    (htrans : IsLocallyTransitive τ p) {W : Scheme.{u}} (g : W ⟶ S) (s t : W ⟶ T)
    (hs : s ≫ p = g) (ht : t ≫ p = g) :
    ∃ (x : Γ(W, ⊤)ˣ) (hx : x ^ n = 1), rootSMul f hζ τ g x (coe_pow_eq_one hx) s = t := by
  set hnS := isUnit_natCast_of_isPrimitiveRoot f hζ
  set R := rootsOfUnityEtaleOver S n hnS
  set E := rootsOfUnityEtaleOverHomEquiv S n hnS
  obtain ⟨O, hO, hOa⟩ := htrans s t (hs.trans ht.symm)
  let 𝒰 := W.openCoverOfIsOpenCover O hO
  have hcompat : ∀ a b : ZMod n, pullback.fst (O a).ι (O b).ι ≫
      ((O a).ι ≫ g ≫ (constRootSection f hζ a).left) =
      pullback.snd (O a).ι (O b).ι ≫ ((O b).ι ≫ g ≫ (constRootSection f hζ b).left) := by
    intro a b
    refine pullback_ι_comp_eq_of_isEmpty O (fun a => g ≫ (constRootSection f hζ a).left)
      (fun a b hab => hfree (pullback.fst (O a).ι (O b).ι ≫ (O a).ι ≫ s) hab ?_) a b
    calc (pullback.fst (O a).ι (O b).ι ≫ (O a).ι ≫ s) ≫ τ a
        = pullback.fst (O a).ι (O b).ι ≫ ((O a).ι ≫ t) := by
          rw [hOa a]; simp only [Category.assoc]
      _ = pullback.snd (O a).ι (O b).ι ≫ ((O b).ι ≫ t) := pullback.condition_assoc _
      _ = pullback.snd (O a).ι (O b).ι ≫ (O b).ι ≫ (s ≫ τ b) := by
          rw [hOa b]
      _ = pullback.fst (O a).ι (O b).ι ≫ (O a).ι ≫ (s ≫ τ b) :=
          (pullback.condition_assoc _).symm
      _ = (pullback.fst (O a).ι (O b).ι ≫ (O a).ι ≫ s) ≫ τ b := by
          simp only [Category.assoc]
  let mL : W ⟶ R.left := 𝒰.glueMorphisms (fun a => (O a).ι ≫ g ≫ (constRootSection f hζ a).left)
    hcompat
  have hmL : ∀ a, (O a).ι ≫ mL = (O a).ι ≫ g ≫ (constRootSection f hζ a).left :=
    𝒰.ι_glueMorphisms (fun a => (O a).ι ≫ g ≫ (constRootSection f hζ a).left) hcompat
  have hmw : mL ≫ R.hom = g := by
    refine 𝒰.hom_ext _ _ fun (a : ZMod n) => ?_
    change (O a).ι ≫ mL ≫ R.hom = (O a).ι ≫ g
    rw [reassoc_of% (hmL a), Over.w]
    exact congrArg ((O a).ι ≫ ·) (Category.comp_id g)
  let m : Over.mk g ⟶ R := Over.homMk mL hmw
  let x0 : Γ(W, ⊤)ˣ := (E _ m).1
  have hx0 : x0 ^ n = 1 := (E _ m).2
  refine ⟨x0, hx0, 𝒰.hom_ext _ _ fun (a : ZMod n) => ?_⟩
  change (O a).ι ≫ _ = (O a).ι ≫ t
  have hlp : ((O a).ι ≫ g) ≫ 𝟙 S = (O a).ι ≫ g := Category.comp_id _
  have e1 := rootsOfUnityEtaleOverHomEquiv_map_left S n hnS
    (Over.homMk (U := Over.mk ((O a).ι ≫ g)) (V := Over.mk g) (O a).ι rfl) m
    (Over.homMk (U := Over.mk ((O a).ι ≫ g)) (V := Over.mk g) (O a).ι rfl ≫ m) rfl
  have e2 := rootsOfUnityEtaleOverHomEquiv_map_left S n hnS
    (Over.homMk (U := Over.mk ((O a).ι ≫ g)) (V := Over.mk (𝟙 S)) ((O a).ι ≫ g) hlp)
    (constRootSection f hζ a)
    (Over.homMk (U := Over.mk ((O a).ι ≫ g)) (V := Over.mk g) (O a).ι rfl ≫ m) (by
      change (O a).ι ≫ mL = ((O a).ι ≫ g) ≫ (constRootSection f hζ a).left
      rw [hmL, Category.assoc])
  have e3 := congrArg Units.val (e1.symm.trans e2)
  simp only [Units.coe_map] at e3
  have hxa : (O a).ι.appTop.hom (x0 : Γ(W, ⊤)) =
      baseRingMap f ((O a).ι ≫ g) (ζ ^ a.val) := by
    refine e3.trans ?_
    rw [constRootSection, Equiv.apply_symm_apply, coe_constRoot]
    change ((O a).ι ≫ g).appTop.hom (baseRingMap f (𝟙 S) (ζ ^ a.val)) = _
    rw [baseRingMap_comp_apply, hlp]
  rw [comp_rootSMul_of_eq f hζ τ g _ _ s (O a).ι a hxa, hOa a]

/-- **Uniqueness in the simple transitivity**: the action is free. -/
theorem rootSMul_injective (hfree : IsFreeTranslation τ) {W : Scheme.{u}} (g : W ⟶ S) (s : W ⟶ T)
    (x y : Γ(W, ⊤)ˣ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : rootSMul f hζ τ g x (coe_pow_eq_one hx) s = rootSMul f hζ τ g y (coe_pow_eq_one hy) s) :
    x = y := by
  refine eq_of_forall_appTop_eq f hζ g
    (W.openCoverOfIsOpenCover _ (isOpenCover_piece_inf_piece f hζ g (x : Γ(W, ⊤)) y)) x y hx hy
    fun ab => ?_
  obtain ⟨a, b⟩ := ab
  set Q := piece f ζ g (x : Γ(W, ⊤)) a ⊓ piece f ζ g (y : Γ(W, ⊤)) b
  change Q.ι.appTop.hom (x : Γ(W, ⊤)) = Q.ι.appTop.hom (y : Γ(W, ⊤))
  obtain ⟨e1, e2⟩ := appTop_ι_piece_inf_piece f hζ g _ _ (coe_pow_eq_one hx)
    (coe_pow_eq_one hy) a b
  by_cases hab : a = b
  · subst hab
    rw [e1, e2]
  · have : IsEmpty Q := by
      refine hfree (Q.ι ≫ s) hab ?_
      have h1 := comp_rootSMul_of_eq f hζ τ g _ (coe_pow_eq_one hx) s Q.ι a e1
      have h2 := comp_rootSMul_of_eq f hζ τ g _ (coe_pow_eq_one hy) s Q.ι b e2
      rw [h] at h1
      simpa only [Category.assoc] using h1.symm.trans h2
    exact Subsingleton.elim _ _

end Transitivity

section Laws

variable {k : Type u} [Field k] [DecidableEq k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) {n : ℕ}
  [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) {T : Scheme.{u}} (τ : ZMod n → (T ⟶ T))

/-- `rootSMul` respects equality of its arguments. -/
theorem rootSMul_congr {W : Scheme.{u}} {g g' : W ⟶ S} (hg : g = g') {x y : Γ(W, ⊤)}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hxy : x = y) {s s' : W ⟶ T} (hs : s = s') :
    rootSMul f hζ τ g x hx s = rootSMul f hζ τ g' y hy s' := by
  subst hg hxy hs; rfl

include hζ in
omit [DecidableEq k] [NeZero n] in
/-- The image of `ζ ^ a` is an `n`-th root of unity. -/
theorem baseRingMap_pow_val_pow {W : Scheme.{u}} (g : W ⟶ S) (a : ZMod n) :
    baseRingMap f g (ζ ^ a.val) ^ n = 1 := by
  rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, map_one]

/-- **The constant root `ζ ^ a` acts by `τ_a`.** -/
theorem rootSMul_baseRingMap {W : Scheme.{u}} (g : W ⟶ S) (a : ZMod n) (s : W ⟶ T) :
    rootSMul f hζ τ g (baseRingMap f g (ζ ^ a.val)) (baseRingMap_pow_val_pow f hζ g a) s =
      s ≫ τ a := by
  have h := comp_rootSMul_of_eq f hζ τ g _ (baseRingMap_pow_val_pow f hζ g a) s (𝟙 W) a
    (by rw [Category.id_comp]; rfl)
  rwa [Category.id_comp, Category.id_comp] at h

/-- If `τ_0 = id`, the root `1` acts trivially. -/
theorem rootSMul_one {W : Scheme.{u}} (g : W ⟶ S) (s : W ⟶ T) (hτ0 : τ 0 = 𝟙 T) :
    rootSMul f hζ τ g 1 (one_pow n) s = s := by
  have h := comp_rootSMul_of_eq f hζ τ g 1 (one_pow n) s (𝟙 W) 0 (by
    rw [map_one, ZMod.val_zero, pow_zero, map_one])
  rwa [Category.id_comp, Category.id_comp, hτ0, Category.comp_id] at h

/-- If `τ_0 = id`, a root of unity equal to `1` acts trivially. -/
theorem rootSMul_eq_of_eq_one {W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (s : W ⟶ T) (hτ0 : τ 0 = 𝟙 T) (h1 : x = 1) : rootSMul f hζ τ g x hx s = s := by
  subst h1
  exact rootSMul_one f hζ τ g s hτ0

/-- The action is compatible with precomposition. -/
theorem rootSMul_naturality {V W : Scheme.{u}} (g : W ⟶ S) (x : Γ(W, ⊤)) (hx : x ^ n = 1)
    (s : W ⟶ T) (h : V ⟶ W) :
    h ≫ rootSMul f hζ τ g x hx s =
      rootSMul f hζ τ (h ≫ g) (h.appTop.hom x) (by rw [← map_pow, hx, map_one]) (h ≫ s) := by
  refine piece_hom_ext f hζ (h ≫ g) (h.appTop.hom x) _ _ fun a => ?_
  have e := appTop_ι_piece f hζ (h ≫ g) (h.appTop.hom x) (by rw [← map_pow, hx, map_one]) a
  rw [ι_rootSMul, ← Category.assoc, comp_rootSMul_of_eq f hζ τ g x hx s _ a (by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, e, Category.assoc])]
  simp only [Category.assoc]

/-- If `τ` is additive, the action is multiplicative: `(x y) • s = x • (y • s)`. -/
theorem rootSMul_mul {W : Scheme.{u}} (g : W ⟶ S) (x y : Γ(W, ⊤)) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (s : W ⟶ T) (hτadd : ∀ a b, τ (a + b) = τ a ≫ τ b) :
    rootSMul f hζ τ g (x * y) (by rw [mul_pow, hx, hy, one_mul]) s =
      rootSMul f hζ τ g x hx (rootSMul f hζ τ g y hy s) := by
  refine (W.openCoverOfIsOpenCover _ (isOpenCover_piece_inf_piece f hζ g x y)).hom_ext _ _
    fun ab => ?_
  obtain ⟨a, b⟩ := ab
  set Q := piece f ζ g x a ⊓ piece f ζ g y b
  change Q.ι ≫ _ = Q.ι ≫ _
  obtain ⟨e1, e2⟩ := appTop_ι_piece_inf_piece f hζ g x y hx hy a b
  have e3 : Q.ι.appTop.hom (x * y) = baseRingMap f (Q.ι ≫ g) (ζ ^ (b + a).val) := by
    rw [map_mul, e1, e2, pow_val_add hζ, map_mul, mul_comm]
  rw [comp_rootSMul_of_eq f hζ τ g _ _ s Q.ι (b + a) e3, ← Category.assoc,
    comp_rootSMul_of_eq f hζ τ g x hx _ Q.ι a e1, ← Category.assoc,
    comp_rootSMul_of_eq f hζ τ g y hy s Q.ι b e2, hτadd]
  simp only [Category.assoc]

end Laws

section Torsor

open Stacks.Cohomology.Torsors

variable {k : Type u} [Field k] [DecidableEq k] {S : Scheme.{u}} (f : S ⟶ Spec (.of k)) {n : ℕ}
  [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
  (τ : ZMod n → (T ⟶ T)) (hτp : ∀ a, τ a ≫ p = p) (hτ0 : τ 0 = 𝟙 T)
  (hτadd : ∀ a b, τ (a + b) = τ a ≫ τ b) (hfree : IsFreeTranslation τ)
  (htrans : IsLocallyTransitive τ p)

/-- The root of unity underlying a section of `μ_n`, read multiplicatively. -/
def sectionRoot (U : S.Etaleᵒᵖ)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    {x : (Γ(U.unop.left, ⊤))ˣ // x ^ n = 1} :=
  rootsOfUnitySection.{u, 0} S n U (Multiplicative.toAdd m)

omit [NeZero n] in
/-- The section `1` of `μ_n` has root `1`. -/
theorem sectionRoot_one (U : S.Etaleᵒᵖ) : (sectionRoot (n := n) U 1).1 = 1 := by
  refine ofUnit_injective.{u, 0} ?_
  rw [sectionRoot, ← rootsOfUnityι_app_eq_ofUnit, ofUnit_one]
  exact map_zero _

omit [NeZero n] in
/-- The root of a product of sections is the product of the roots. -/
theorem sectionRoot_mul (U : S.Etaleᵒᵖ)
    (m m' : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    (sectionRoot U (m * m')).1 = (sectionRoot U m).1 * (sectionRoot U m').1 := by
  refine ofUnit_injective.{u, 0} ?_
  change _ = ofUnit.{u, 0} (sectionRoot U m).1 + ofUnit.{u, 0} (sectionRoot U m').1
  rw [sectionRoot, sectionRoot, sectionRoot, ← rootsOfUnityι_app_eq_ofUnit,
    ← rootsOfUnityι_app_eq_ofUnit, ← rootsOfUnityι_app_eq_ofUnit, ← map_add]
  rfl

omit [NeZero n] in
/-- The root of a section is compatible with restriction. -/
theorem sectionRoot_map {U V : S.Etaleᵒᵖ} (g : U ⟶ V)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    (sectionRoot V ((abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.map g m)).1 =
      Units.map g.unop.left.appTop.hom.toMonoidHom (sectionRoot U m).1 :=
  rootsOfUnitySection_naturality.{u, 0} S n g.unop (Multiplicative.toAdd m)

/-- The root of unity underlying a section of `μ_n`, as a function. -/
abbrev sectionRootVal (U : S.Etaleᵒᵖ)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    Γ(U.unop.left, ⊤) :=
  (((sectionRoot U m).1 : (Γ(U.unop.left, ⊤))ˣ) : Γ(U.unop.left, ⊤))

omit [NeZero n] in
/-- The function underlying a section of `μ_n` has `n`-th power one. -/
theorem sectionRootVal_pow (U : S.Etaleᵒᵖ)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    sectionRootVal U m ^ n = 1 :=
  coe_pow_eq_one (sectionRoot U m).2

omit [NeZero n] in
/-- The function underlying the section `1` of `μ_n` is `1`. -/
theorem sectionRootVal_one (U : S.Etaleᵒᵖ) : sectionRootVal (n := n) U 1 = 1 :=
  (congrArg Units.val (sectionRoot_one U)).trans Units.val_one

omit [NeZero n] in
/-- The function underlying a product of sections is the product of the functions. -/
theorem sectionRootVal_mul (U : S.Etaleᵒᵖ)
    (m m' : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    sectionRootVal U (m * m') = sectionRootVal U m * sectionRootVal U m' :=
  (congrArg Units.val (sectionRoot_mul U m m')).trans (Units.val_mul _ _)

omit [NeZero n] in
/-- The function underlying a section is compatible with restriction. -/
theorem sectionRootVal_map {U V : S.Etaleᵒᵖ} (g : U ⟶ V)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U) :
    sectionRootVal V ((abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.map g m) =
      g.unop.left.appTop.hom (sectionRootVal U m) :=
  congrArg Units.val (sectionRoot_map g m)

omit [NeZero n] in
/-- Sections of `μ_n` are exactly the `n`-th roots of unity in the global functions. -/
theorem sectionRoot_bijective (U : S.Etaleᵒᵖ) :
    Function.Bijective (sectionRoot (n := n) U) :=
  (rootsOfUnitySection_bijective.{u, 0} S n U).comp Multiplicative.toAdd.bijective

include hτp in
/-- The action of a section of `μ_n` on a section of `T`. -/
def schemeTorsorAct (U : S.Etaleᵒᵖ)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U)
    (σ : (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk p)).obj U) :
    (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk p)).obj U :=
  ULift.up (MorphismProperty.Over.homMk
    (rootSMul f hζ τ U.unop.hom (sectionRootVal U m) (sectionRootVal_pow U m) σ.down.left)
    (rootSMul_comp f hζ τ _ _ _ hτp _ (MorphismProperty.Over.w σ.down)))

/-- The morphism underlying the action of `m` on `σ` is `m • σ`. -/
theorem schemeTorsorAct_left (U : S.Etaleᵒᵖ)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U)
    (σ : (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk p)).obj U) :
    (schemeTorsorAct f hζ p τ hτp U m σ).down.left =
      rootSMul f hζ τ U.unop.hom (sectionRootVal U m) (sectionRootVal_pow U m) σ.down.left := rfl

/-- A section of `μ_n` whose function is `ζ ^ a` acts by `τ_a`. -/
private theorem schemeTorsorAct_left_of_eq (U : S.Etaleᵒᵖ)
    (m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U)
    (σ : (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk p)).obj U) (a : ZMod n)
    (hm : sectionRootVal U m = baseRingMap f U.unop.hom (ζ ^ a.val)) :
    (schemeTorsorAct f hζ p τ hτp U m σ).down.left = σ.down.left ≫ τ a :=
  (schemeTorsorAct_left f hζ p τ hτp U m σ).trans
    ((rootSMul_congr f hζ τ rfl _ (baseRingMap_pow_val_pow f hζ _ a) hm rfl).trans
      (rootSMul_baseRingMap f hζ τ _ a _))

include hτ0 hτadd hfree htrans in
/-- **The `μ_n`-torsor of sections of a `ℤ/n`-torsor scheme**, as a pseudo-torsor. -/
def schemePseudoTorsor :
    PseudoTorsor.{u + 1} (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)) where
  presheaf := uliftYoneda.{u + 1}.obj (Scheme.Etale.mk p)
  isSheaf := ((S.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Scheme.Etale.mk p)).property
  act := schemeTorsorAct f hζ p τ hτp
  one_act U σ := by
    refine ULift.ext (MorphismProperty.Over.Hom.ext ?_)
    rw [schemeTorsorAct_left]
    exact rootSMul_eq_of_eq_one f hζ τ _ _ _ _ hτ0 (sectionRootVal_one U)
  mul_act U m m' σ := by
    refine ULift.ext (MorphismProperty.Over.Hom.ext ?_)
    rw [schemeTorsorAct_left, schemeTorsorAct_left, schemeTorsorAct_left]
    refine (rootSMul_congr f hζ τ rfl _
      (by rw [mul_pow, sectionRootVal_pow, sectionRootVal_pow, one_mul])
      (sectionRootVal_mul U m m') rfl).trans ?_
    exact rootSMul_mul f hζ τ U.unop.hom _ _ (sectionRootVal_pow U m)
      (sectionRootVal_pow U m') σ.down.left hτadd
  naturality {U V} g m σ := by
    refine ULift.ext (MorphismProperty.Over.Hom.ext ?_)
    change g.unop.left ≫ (schemeTorsorAct f hζ p τ hτp U m σ).down.left =
      (schemeTorsorAct f hζ p τ hτp V _ _).down.left
    rw [schemeTorsorAct_left, schemeTorsorAct_left]
    refine (rootSMul_naturality f hζ τ _ _ _ _ g.unop.left).trans ?_
    exact rootSMul_congr f hζ τ (MorphismProperty.Over.w g.unop) _ _
      (sectionRootVal_map g m).symm rfl
  simplyTransitive U _ σ σ' := by
    obtain ⟨x, hx, hxs⟩ := exists_rootSMul_eq f hζ τ hfree htrans U.unop.hom σ.down.left
      σ'.down.left (MorphismProperty.Over.w σ.down) (MorphismProperty.Over.w σ'.down)
    obtain ⟨m, hm⟩ := (sectionRoot_bijective U).2 ⟨x, hx⟩
    have hmx : sectionRootVal U m = x.val := congrArg (fun z => z.1.val) hm
    refine ⟨m, ?_, fun m' hm' => ?_⟩
    · refine ULift.ext (MorphismProperty.Over.Hom.ext ?_)
      rw [schemeTorsorAct_left]
      exact (rootSMul_congr f hζ τ rfl _ _ hmx rfl).trans hxs
    · apply (sectionRoot_bijective U).1
      rw [hm]
      apply Subtype.ext
      refine rootSMul_injective f hζ τ hfree U.unop.hom σ.down.left _ _ (sectionRoot U m').2 hx ?_
      have h1 := congrArg (fun z => z.down.left) hm'
      simp only [schemeTorsorAct_left] at h1
      exact h1.trans hxs.symm

include hτ0 hτadd hfree htrans in
/-- The sections of a surjective `ℤ/n`-torsor scheme exist étale locally. -/
theorem schemePseudoTorsor_isTorsor [Surjective p] :
    (schemePseudoTorsor f hζ p τ hτp hτ0 hτadd hfree htrans).IsTorsor := by
  intro U
  let V : S.Etale := Scheme.Etale.mk (pullback.fst U.hom p ≫ U.hom)
  let j : V ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom p) rfl
  let σ : V ⟶ Scheme.Etale.mk p :=
    MorphismProperty.Over.homMk (pullback.snd U.hom p) pullback.condition.symm
  refine ⟨Sieve.ofArrows (fun _ : Unit => V) (fun _ => j), ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨(), ?_⟩
    exact (pullback.fst U.hom p).surjective x
  · intro W h hh
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
    exact ⟨ULift.up (a ≫ σ)⟩

/-- **The `μ_n`-torsor of sections of a surjective étale `ℤ/n`-torsor scheme.** -/
def schemeTorsor [Surjective p] : AbelianTorsor (rootsOfUnitySheaf.{u, 0} S n) :=
  ⟨schemePseudoTorsor f hζ p τ hτp hτ0 hτadd hfree htrans,
    schemePseudoTorsor_isTorsor f hζ p τ hτp hτ0 hτadd hfree htrans⟩

include hζ in
omit [DecidableEq k] in
/-- Every section `ζ ^ a` is a section of `μ_n`. -/
theorem exists_sectionRootVal_eq (U : S.Etaleᵒᵖ) (a : ZMod n) :
    ∃ m : (abelianSheafAsGroupSheaf (rootsOfUnitySheaf.{u, 0} S n)).presheaf.obj U,
      sectionRootVal U m = baseRingMap f U.unop.hom (ζ ^ a.val) := by
  obtain ⟨m, hm⟩ :=
    (sectionRoot_bijective U).2 ⟨constRoot f hζ U.unop.hom a, constRoot_pow f hζ _ a⟩
  exact ⟨m, congrArg (fun z => z.1.val) hm⟩

/-- **An equivariant morphism of `μ_n`-torsors of sections is induced by an equivariant morphism
of the torsor schemes.** -/
theorem exists_hom_of_pseudoTorsorHom {T₁ T₂ : Scheme.{u}} (p₁ : T₁ ⟶ S) (p₂ : T₂ ⟶ S)
    [Etale p₁] [Etale p₂]
    (τ₁ : ZMod n → (T₁ ⟶ T₁)) (τ₂ : ZMod n → (T₂ ⟶ T₂)) (hτp₁ : ∀ a, τ₁ a ≫ p₁ = p₁)
    (hτp₂ : ∀ a, τ₂ a ≫ p₂ = p₂) (hτ0₁ : τ₁ 0 = 𝟙 T₁) (hτ0₂ : τ₂ 0 = 𝟙 T₂)
    (hτadd₁ : ∀ a b, τ₁ (a + b) = τ₁ a ≫ τ₁ b) (hτadd₂ : ∀ a b, τ₂ (a + b) = τ₂ a ≫ τ₂ b)
    (hfree₁ : IsFreeTranslation τ₁) (hfree₂ : IsFreeTranslation τ₂)
    (htrans₁ : IsLocallyTransitive τ₁ p₁) (htrans₂ : IsLocallyTransitive τ₂ p₂)
    (e : (schemePseudoTorsor f hζ p₁ τ₁ hτp₁ hτ0₁ hτadd₁ hfree₁ htrans₁).Hom
      (schemePseudoTorsor f hζ p₂ τ₂ hτp₂ hτ0₂ hτadd₂ hfree₂ htrans₂)) :
    ∃ φ : T₁ ⟶ T₂, φ ≫ p₂ = p₁ ∧ ∀ a, τ₁ a ≫ φ = φ ≫ τ₂ a := by
  set U : S.Etaleᵒᵖ := op (Scheme.Etale.mk p₁)
  let x₀ : (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk p₁)).obj U := ULift.up (𝟙 _)
  let φ' : Scheme.Etale.mk p₁ ⟶ Scheme.Etale.mk p₂ := (e.hom.app U x₀).down
  refine ⟨φ'.left, MorphismProperty.Over.w φ', fun a => ?_⟩
  obtain ⟨m, hm⟩ := exists_sectionRootVal_eq f hζ U a
  let τ' : Scheme.Etale.mk p₁ ⟶ Scheme.Etale.mk p₁ := MorphismProperty.Over.homMk (τ₁ a) (hτp₁ a)
  have hact := e.map_act U m x₀
  have hnat := NatTrans.naturality_apply e.hom τ'.op x₀
  have e1 : (schemeTorsorAct f hζ p₁ τ₁ hτp₁ U m x₀).down.left = τ₁ a := by
    exact (schemeTorsorAct_left_of_eq f hζ p₁ τ₁ hτp₁ U m _ a hm).trans (Category.id_comp _)
  have e2 : schemeTorsorAct f hζ p₁ τ₁ hτp₁ U m x₀ =
      (schemePseudoTorsor f hζ p₁ τ₁ hτp₁ hτ0₁ hτadd₁ hfree₁ htrans₁).presheaf.map τ'.op x₀ :=
    ULift.ext (MorphismProperty.Over.Hom.ext (e1.trans (Category.comp_id _).symm))
  have e3 : (schemeTorsorAct f hζ p₂ τ₂ hτp₂ U m (e.hom.app U x₀)).down.left =
      φ'.left ≫ τ₂ a := by
    exact schemeTorsorAct_left_of_eq f hζ p₂ τ₂ hτp₂ U m _ a hm
  have hact' : e.hom.app U (schemeTorsorAct f hζ p₁ τ₁ hτp₁ U m x₀) =
      schemeTorsorAct f hζ p₂ τ₂ hτp₂ U m (e.hom.app U x₀) := hact
  rw [e2] at hact'
  replace hact' := hnat.symm.trans hact'
  exact (congrArg (fun z => z.down.left) hact').trans e3

/-- **Torsor schemes with the same `μ_n`-torsor class are related by an equivariant morphism.** -/
theorem exists_hom_of_schemeTorsor_eq {T₁ T₂ : Scheme.{u}} (p₁ : T₁ ⟶ S) (p₂ : T₂ ⟶ S)
    [Etale p₁] [Etale p₂] [Surjective p₁] [Surjective p₂]
    (τ₁ : ZMod n → (T₁ ⟶ T₁)) (τ₂ : ZMod n → (T₂ ⟶ T₂)) (hτp₁ : ∀ a, τ₁ a ≫ p₁ = p₁)
    (hτp₂ : ∀ a, τ₂ a ≫ p₂ = p₂) (hτ0₁ : τ₁ 0 = 𝟙 T₁) (hτ0₂ : τ₂ 0 = 𝟙 T₂)
    (hτadd₁ : ∀ a b, τ₁ (a + b) = τ₁ a ≫ τ₁ b) (hτadd₂ : ∀ a b, τ₂ (a + b) = τ₂ a ≫ τ₂ b)
    (hfree₁ : IsFreeTranslation τ₁) (hfree₂ : IsFreeTranslation τ₂)
    (htrans₁ : IsLocallyTransitive τ₁ p₁) (htrans₂ : IsLocallyTransitive τ₂ p₂)
    (h : Quotient.mk (torsorSetoid (rootsOfUnitySheaf.{u, 0} S n))
        (schemeTorsor f hζ p₁ τ₁ hτp₁ hτ0₁ hτadd₁ hfree₁ htrans₁) =
      Quotient.mk (torsorSetoid (rootsOfUnitySheaf.{u, 0} S n))
        (schemeTorsor f hζ p₂ τ₂ hτp₂ hτ0₂ hτadd₂ hfree₂ htrans₂)) :
    ∃ φ : T₁ ⟶ T₂, φ ≫ p₂ = p₁ ∧ ∀ a, τ₁ a ≫ φ = φ ≫ τ₂ a := by
  obtain ⟨e, -⟩ := Quotient.exact h
  exact exists_hom_of_pseudoTorsorHom f hζ p₁ p₂ τ₁ τ₂ hτp₁ hτp₂ hτ0₁ hτ0₂ hτadd₁ hτadd₂ hfree₁
    hfree₂ htrans₁ htrans₂ e

end Torsor

end Stacks.Kummer
