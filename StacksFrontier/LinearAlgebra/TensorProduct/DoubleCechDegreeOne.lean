module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic

/-!
# Degree-one cocycles of a Čech double complex over a field

Let `K` be a field. Consider a complex `C₀ → C₁ → C₂` of `K`-vector spaces (the Čech complex of
the structure sheaf of a scheme `X` for a finite affine cover, in degrees `≤ 2`) whose degree-zero
cohomology is spanned by an element `one`, and on the other side a finite family of `K`-vector
spaces `B₁ b` with restriction maps `B₁ b → B₂ b b'` forming an equalizer with global sections
`G` (the structure sheaf of a scheme `Y` on a finite affine cover, possibly tensored with a
vector space of coefficients).

A degree-one cocycle of the total complex of the double complex `C ⊗ B` is a pair
`(c₁₀, c₀₁)` with `c₁₀ b ∈ C₁ ⊗ B₁ b` and `c₀₁ b b' ∈ C₀ ⊗ B₂ b b'` satisfying the two
cocycle conditions that involve `c₁₀`. The main result,
`Stacks.DoubleCech.exists_eq_coboundary`, says that such a cocycle is a coboundary as soon as
its restrictions to the two "faces" are: its image under an evaluation `B₁ b₀ → G` that splits
the inclusion of global sections, and its image under an evaluation `C₀ → K` taking `one` to
`1`.

This is the linear algebra behind the injectivity of
`H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` along the two faces `X × y` and `x × Y`, which is the
Künneth input of the theorem of the cube
([Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3), through
[Stacks, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)). The argument is the Leray
argument for the projection to `Y`: for each `b` the class of `c₁₀ b` in `H¹(C) ⊗ B₁ b` is
compatible on overlaps, hence a constant, which vanishes because it vanishes at the face;
correcting by a coboundary kills `c₁₀`, and what remains of `c₀₁` is a Čech cocycle of the second
factor, which is a coboundary by the other face.

## Main results

* `Stacks.DoubleCech.exists_lTensor_eq_of_equalizer`: an equalizer of vector spaces stays an
  equalizer after tensoring with any vector space.
* `Stacks.DoubleCech.exists_eq_coboundary`: the degree-one statement described above.
-/

@[expose] public section

open TensorProduct LinearMap

namespace Stacks.DoubleCech

variable {K : Type*} [Field K]

section Equalizer

variable {J : Type*} [Fintype J] [DecidableEq J] {G : Type*} [AddCommGroup G] [Module K G]
  {B₁ : J → Type*} [∀ b, AddCommGroup (B₁ b)] [∀ b, Module K (B₁ b)]
  {B₂ : J → J → Type*} [∀ b b', AddCommGroup (B₂ b b')] [∀ b b', Module K (B₂ b b')]
  (incl : ∀ b, G →ₗ[K] B₁ b) (s₀ : ∀ b b', B₁ b →ₗ[K] B₂ b b')
  (s₁ : ∀ b b', B₁ b' →ₗ[K] B₂ b b')

/-- The difference map `(g_b) ↦ (s₀ g_b - s₁ g_{b'})` of an equalizer. -/
def eqDiff : (∀ b, B₁ b) →ₗ[K] ∀ p : J × J, B₂ p.1 p.2 :=
  LinearMap.pi fun p => s₀ p.1 p.2 ∘ₗ LinearMap.proj p.1 - s₁ p.1 p.2 ∘ₗ LinearMap.proj p.2

/-- The inclusion of global sections into the product. -/
def eqIncl : G →ₗ[K] ∀ b, B₁ b := LinearMap.pi incl

variable {incl s₀ s₁}

omit [Fintype J] [DecidableEq J] in
/-- If the restriction maps agree on global sections and every compatible family comes from a
global section, then `eqIncl incl` and `eqDiff s₀ s₁` form an exact sequence. -/
theorem exact_eqIncl_eqDiff (hcompat : ∀ b b', s₀ b b' ∘ₗ incl b = s₁ b b' ∘ₗ incl b')
    (heq : ∀ g : ∀ b, B₁ b, (∀ b b', s₀ b b' (g b) = s₁ b b' (g b')) →
      ∃ θ : G, ∀ b, g b = incl b θ) :
    Function.Exact (eqIncl incl) (eqDiff s₀ s₁) := by
  intro g
  constructor
  · intro hg
    obtain ⟨θ, hθ⟩ := heq g fun b b' => by
      simpa [eqDiff, sub_eq_zero] using congrFun hg (b, b')
    exact ⟨θ, funext fun b => (hθ b).symm⟩
  · rintro ⟨θ, rfl⟩
    funext p
    simpa [eqDiff, eqIncl, sub_eq_zero] using LinearMap.congr_fun (hcompat p.1 p.2) θ

variable (H : Type*) [AddCommGroup H] [Module K H]

omit [Fintype J] [DecidableEq J] in
/-- Under `TensorProduct.piRightHom`, the component at `p` of `lTensor H (eqDiff s₀ s₁) x` is the
difference of the restrictions of the components of `x` at `p.1` and `p.2`. -/
theorem piRight_lTensor_eqDiff (x : H ⊗[K] (∀ b, B₁ b)) (p : J × J) :
    TensorProduct.piRightHom K K H (fun p : J × J => B₂ p.1 p.2)
        (lTensor H (eqDiff s₀ s₁) x) p =
      lTensor H (s₀ p.1 p.2) (TensorProduct.piRightHom K K H B₁ x p.1) -
        lTensor H (s₁ p.1 p.2) (TensorProduct.piRightHom K K H B₁ x p.2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul h g => simp [eqDiff, tmul_sub]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
    abel

omit [Fintype J] [DecidableEq J] in
/-- Under `TensorProduct.piRightHom`, the component at `b` of `lTensor H (eqIncl incl) θ` is
`lTensor H (incl b) θ`. -/
theorem piRight_lTensor_eqIncl (θ : H ⊗[K] G) (b : J) :
    TensorProduct.piRightHom K K H B₁ (lTensor H (eqIncl incl) θ) b = lTensor H (incl b) θ := by
  induction θ using TensorProduct.induction_on with
  | zero => simp
  | tmul h g => simp [eqIncl]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- **An equalizer of vector spaces stays an equalizer after tensoring.** If `G` is the
equalizer of the two restriction maps `∏ B₁ b ⇉ ∏ B₂ b b'`, then for every vector space `H` a
family `h_b ∈ H ⊗ B₁ b` compatible on overlaps comes from an element of `H ⊗ G`. -/
theorem exists_lTensor_eq_of_equalizer
    (hcompat : ∀ b b', s₀ b b' ∘ₗ incl b = s₁ b b' ∘ₗ incl b')
    (heq : ∀ g : ∀ b, B₁ b, (∀ b b', s₀ b b' (g b) = s₁ b b' (g b')) →
      ∃ θ : G, ∀ b, g b = incl b θ)
    (h : ∀ b, H ⊗[K] B₁ b)
    (hh : ∀ b b', lTensor H (s₀ b b') (h b) = lTensor H (s₁ b b') (h b')) :
    ∃ θ : H ⊗[K] G, ∀ b, h b = lTensor H (incl b) θ := by
  have hex := Module.Flat.lTensor_exact H (exact_eqIncl_eqDiff hcompat heq)
  set x := (TensorProduct.piRight K K H B₁).symm h
  have hxh : ∀ b, TensorProduct.piRightHom K K H B₁ x b = h b := fun b => by
    have := congrFun ((TensorProduct.piRight K K H B₁).apply_symm_apply h) b
    rwa [TensorProduct.piRight_apply] at this
  have hzero : lTensor H (eqDiff s₀ s₁) x = 0 := by
    apply (TensorProduct.piRight K K H (fun p : J × J => B₂ p.1 p.2)).injective
    funext p
    rw [TensorProduct.piRight_apply, piRight_lTensor_eqDiff, hxh, hxh, hh, sub_self]
    simp
  obtain ⟨θ, hθ⟩ := (hex x).1 hzero
  refine ⟨θ, fun b => ?_⟩
  rw [← hxh b, ← hθ, piRight_lTensor_eqIncl]

end Equalizer

section Commute

variable {M N P Q : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]

/-- The maps `rTensor Q f` and `lTensor M g` commute on `M ⊗ N`. -/
theorem rTensor_lTensor_apply (f : M →ₗ[K] P) (g : N →ₗ[K] Q) (x : M ⊗[K] N) :
    rTensor Q f (lTensor M g x) = lTensor P g (rTensor N f x) := by
  rw [← LinearMap.comp_apply, rTensor_comp_lTensor, ← LinearMap.comp_apply, lTensor_comp_rTensor]

/-- For `f : M → K`, applying `lTensor M g`, then `rTensor Q f` and `TensorProduct.lid` agrees
with applying `rTensor N f` and `TensorProduct.lid`, then `g`. -/
theorem lid_rTensor_lTensor_apply (f : M →ₗ[K] K) (g : N →ₗ[K] Q) (x : M ⊗[K] N) :
    TensorProduct.lid K Q (rTensor Q f (lTensor M g x)) =
      g (TensorProduct.lid K N (rTensor N f x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Commute

section Main

variable {C₀ C₁ C₂ : Type*} [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]
  [AddCommGroup C₂] [Module K C₂] {dX₀ : C₀ →ₗ[K] C₁} {dX₁ : C₁ →ₗ[K] C₂}
  {J : Type*} [Fintype J] [DecidableEq J] {G : Type*} [AddCommGroup G] [Module K G]
  {B₁ : J → Type*} [∀ b, AddCommGroup (B₁ b)] [∀ b, Module K (B₁ b)]
  {B₂ : J → J → Type*} [∀ b b', AddCommGroup (B₂ b b')] [∀ b b', Module K (B₂ b b')]
  {incl : ∀ b, G →ₗ[K] B₁ b} {s₀ : ∀ b b', B₁ b →ₗ[K] B₂ b b'}
  {s₁ : ∀ b b', B₁ b' →ₗ[K] B₂ b b'}

/-- The corestriction of `dX₀` to the cocycles of degree one. -/
def dCod (hdd : dX₁ ∘ₗ dX₀ = 0) : C₀ →ₗ[K] LinearMap.ker dX₁ :=
  dX₀.codRestrict (LinearMap.ker dX₁) fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd, LinearMap.zero_apply]

/-- Composing `dCod hdd` with the inclusion of `ker dX₁` recovers `dX₀`. -/
theorem subtype_comp_dCod (hdd : dX₁ ∘ₗ dX₀ = 0) :
    (LinearMap.ker dX₁).subtype ∘ₗ dCod hdd = dX₀ := rfl

/-- The first cohomology `ker dX₁ / im dX₀`. -/
abbrev H1 (hdd : dX₁ ∘ₗ dX₀ = 0) := LinearMap.ker dX₁ ⧸ LinearMap.range (dCod hdd)

/-- The quotient map onto `H1 hdd` kills the coboundaries. -/
private theorem mkQ_comp_dCod (hdd : dX₁ ∘ₗ dX₀ = 0) :
    (LinearMap.range (dCod hdd)).mkQ ∘ₗ dCod hdd = 0 := by
  ext x
  simp

/-- Tensored with `M`, the inclusion of `ker dX₁` after `dCod hdd` recovers `dX₀`. -/
private theorem rTensor_subtype_rTensor_dCod (hdd : dX₁ ∘ₗ dX₀ = 0) (M : Type*) [AddCommGroup M]
    [Module K M] (x : C₀ ⊗[K] M) :
    rTensor M (LinearMap.ker dX₁).subtype (rTensor M (dCod hdd) x) = rTensor M dX₀ x := by
  rw [← LinearMap.comp_apply (rTensor M (LinearMap.ker dX₁).subtype), ← rTensor_comp,
    subtype_comp_dCod]

/-- Tensored with `M`, a coboundary has zero class in `H1 hdd`. -/
private theorem rTensor_mkQ_rTensor_dCod (hdd : dX₁ ∘ₗ dX₀ = 0) (M : Type*) [AddCommGroup M]
    [Module K M] (x : C₀ ⊗[K] M) :
    rTensor M (LinearMap.range (dCod hdd)).mkQ (rTensor M (dCod hdd) x) = 0 := by
  rw [← LinearMap.comp_apply (rTensor M (LinearMap.range (dCod hdd)).mkQ), ← rTensor_comp,
    mkQ_comp_dCod, rTensor_zero, LinearMap.zero_apply]

/-- Tensoring the inclusion of `ker dX₁` into `C₁` with a vector space `M` is injective. -/
theorem rTensor_subtype_injective (M : Type*) [AddCommGroup M] [Module K M] :
    Function.Injective (rTensor M (LinearMap.ker dX₁).subtype) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)

/-- A cocycle with coefficients is a cocycle tensored with the coefficients. -/
theorem exists_rTensor_subtype_eq (M : Type*) [AddCommGroup M] [Module K M] (z : C₁ ⊗[K] M)
    (hz : rTensor M dX₁ z = 0) :
    ∃ z' : LinearMap.ker dX₁ ⊗[K] M, rTensor M (LinearMap.ker dX₁).subtype z' = z :=
  ((Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map dX₁)) z).1 hz

/-- A cocycle with coefficients whose class vanishes is a coboundary. -/
theorem exists_rTensor_dCod_eq (hdd : dX₁ ∘ₗ dX₀ = 0) (M : Type*) [AddCommGroup M]
    [Module K M] (z' : LinearMap.ker dX₁ ⊗[K] M)
    (hz : rTensor M (LinearMap.range (dCod hdd)).mkQ z' = 0) :
    ∃ f : C₀ ⊗[K] M, rTensor M (dCod hdd) f = z' := by
  have hex : Function.Exact (dCod hdd) (LinearMap.range (dCod hdd)).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  exact ((rTensor_exact M hex (Submodule.mkQ_surjective _)) z').1 hz

/-- A degree-zero cocycle with coefficients in `M` is `one` tensored with an element of `M`. -/
private theorem exists_eq_one_tmul_of_rTensor_eq_zero {one : C₀} (hone : dX₀ one = 0)
    (hker : ∀ f : C₀, dX₀ f = 0 → ∃ t : K, f = t • one) (M : Type*) [AddCommGroup M]
    [Module K M] (c : C₀ ⊗[K] M) (hc : rTensor M dX₀ c = 0) : ∃ g : M, c = one ⊗ₜ g := by
  let τ : K →ₗ[K] LinearMap.ker dX₀ := LinearMap.toSpanSingleton K _ ⟨one, hone⟩
  have hτ : Function.Surjective τ := by
    rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := hker x hx
    exact ⟨t, rfl⟩
  obtain ⟨w, hw⟩ := ((Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map dX₀)) c).1 hc
  obtain ⟨u, rfl⟩ := rTensor_surjective M hτ w
  refine ⟨TensorProduct.lid K _ u, ?_⟩
  rw [← hw, ← LinearMap.comp_apply, ← rTensor_comp]
  conv_lhs => rw [← (TensorProduct.lid K M).symm_apply_apply u]
  rw [TensorProduct.lid_symm_apply, rTensor_tmul]
  simp [τ]

/-- Tensored with `M`, a cocycle which becomes a coboundary in `C₁ ⊗ M` has zero class. -/
private theorem rTensor_mkQ_eq_zero_of_rTensor_subtype_eq (hdd : dX₁ ∘ₗ dX₀ = 0) (M : Type*)
    [AddCommGroup M] [Module K M] (z' : LinearMap.ker dX₁ ⊗[K] M) (e : C₀ ⊗[K] M)
    (h : rTensor M (LinearMap.ker dX₁).subtype z' = rTensor M dX₀ e) :
    rTensor M (LinearMap.range (dCod hdd)).mkQ z' = 0 := by
  rw [rTensor_subtype_injective M (h.trans (rTensor_subtype_rTensor_dCod hdd M e).symm),
    rTensor_mkQ_rTensor_dCod]

omit [Fintype J] [DecidableEq J] in
/-- The classes in `H1 hdd ⊗ B₁ b` of the `C₁ ⊗ B₁` part of a total cocycle are compatible on
overlaps. -/
private theorem lTensor_rTensor_mkQ_eq (hdd : dX₁ ∘ₗ dX₀ = 0) {c₁₀ : ∀ b, C₁ ⊗[K] B₁ b}
    {c₀₁ : ∀ b b', C₀ ⊗[K] B₂ b b'}
    (hE11 : ∀ b b', lTensor C₁ (s₁ b b') (c₁₀ b') - lTensor C₁ (s₀ b b') (c₁₀ b) =
      rTensor (B₂ b b') dX₀ (c₀₁ b b'))
    {z' : ∀ b, LinearMap.ker dX₁ ⊗[K] B₁ b}
    (hz' : ∀ b, rTensor (B₁ b) (LinearMap.ker dX₁).subtype (z' b) = c₁₀ b) (b b' : J) :
    lTensor (H1 hdd) (s₀ b b') (rTensor (B₁ b) (LinearMap.range (dCod hdd)).mkQ (z' b)) =
      lTensor (H1 hdd) (s₁ b b') (rTensor (B₁ b') (LinearMap.range (dCod hdd)).mkQ (z' b')) := by
  have := rTensor_mkQ_eq_zero_of_rTensor_subtype_eq hdd (B₂ b b')
    (lTensor _ (s₁ b b') (z' b') - lTensor _ (s₀ b b') (z' b)) (c₀₁ b b') (by
      rw [map_sub, rTensor_lTensor_apply, rTensor_lTensor_apply, hz', hz', hE11])
  rw [map_sub, rTensor_lTensor_apply, rTensor_lTensor_apply, sub_eq_zero] at this
  exact this.symm

/-- The `C₁ ⊗ B₁` part of a total degree-one cocycle is a coboundary of the first factor as soon
as its evaluation along a retraction `evY` of `incl b₀` is. -/
private theorem exists_eq_rTensor_of_face (hdd : dX₁ ∘ₗ dX₀ = 0)
    (hcompat : ∀ b b', s₀ b b' ∘ₗ incl b = s₁ b b' ∘ₗ incl b')
    (heq : ∀ g : ∀ b, B₁ b, (∀ b b', s₀ b b' (g b) = s₁ b b' (g b')) →
      ∃ θ : G, ∀ b, g b = incl b θ)
    (b₀ : J) (evY : B₁ b₀ →ₗ[K] G) (hevY : evY ∘ₗ incl b₀ = LinearMap.id)
    (c₁₀ : ∀ b, C₁ ⊗[K] B₁ b) (c₀₁ : ∀ b b', C₀ ⊗[K] B₂ b b')
    (hE20 : ∀ b, rTensor (B₁ b) dX₁ (c₁₀ b) = 0)
    (hE11 : ∀ b b', lTensor C₁ (s₁ b b') (c₁₀ b') - lTensor C₁ (s₀ b b') (c₁₀ b) =
      rTensor (B₂ b b') dX₀ (c₀₁ b b'))
    (hfaceX : ∃ eX : C₀ ⊗[K] G, lTensor C₁ evY (c₁₀ b₀) = rTensor G dX₀ eX) (b : J) :
    ∃ f : C₀ ⊗[K] B₁ b, c₁₀ b = rTensor (B₁ b) dX₀ f := by
  obtain ⟨eX, heX⟩ := hfaceX
  choose z' hz' using fun b => exists_rTensor_subtype_eq (B₁ b) (c₁₀ b) (hE20 b)
  set h : ∀ b, H1 hdd ⊗[K] B₁ b :=
    fun b => rTensor (B₁ b) (LinearMap.range (dCod hdd)).mkQ (z' b) with hh
  obtain ⟨θ, hθ⟩ := exists_lTensor_eq_of_equalizer (H1 hdd) hcompat heq h
    (lTensor_rTensor_mkQ_eq hdd hE11 hz')
  have hface : lTensor (H1 hdd) evY (h b₀) = 0 := by
    simp only [hh]
    rw [← rTensor_lTensor_apply]
    exact rTensor_mkQ_eq_zero_of_rTensor_subtype_eq hdd G _ eX
      (by rw [rTensor_lTensor_apply, hz', heX])
  rw [hθ b₀, ← LinearMap.comp_apply, ← lTensor_comp, hevY, lTensor_id,
    LinearMap.id_apply] at hface
  have h0 : h b = 0 := by rw [hθ b, hface, map_zero]
  obtain ⟨f, hf⟩ := exists_rTensor_dCod_eq hdd (B₁ b) (z' b) h0
  exact ⟨f, by rw [← hz', ← hf, rTensor_subtype_rTensor_dCod]⟩

/-- **A total degree-one cocycle of `C ⊗ B` whose two face restrictions are coboundaries is a
coboundary.**

The hypotheses are: `dX₁ ∘ dX₀ = 0`; `one` spans the kernel of `dX₀` and is taken to `1` by the
evaluation `evX`; the restriction maps `s₀, s₁` of the second factor make `G` (through `incl`)
their equalizer and `evY : B₁ b₀ → G` retracts `incl b₀`. The cochain consists of
`c₁₀ b ∈ C₁ ⊗ B₁ b` and `c₀₁ b b' ∈ C₀ ⊗ B₂ b b'`, satisfying `hE20` (each `c₁₀ b` is a
cocycle of the first factor) and `hE11` (the mixed cocycle condition). `hfaceX` says that the
evaluation of `c₁₀ b₀` along `evY` is a coboundary of the first factor, and `hfaceY` that the
evaluation of `c₀₁` along `evX` is a Čech coboundary of the second factor. The conclusion is a
`0`-cochain `e b ∈ C₀ ⊗ B₁ b` whose total coboundary is `(c₁₀, c₀₁)`. -/
theorem exists_eq_coboundary (hdd : dX₁ ∘ₗ dX₀ = 0) (one : C₀) (hone : dX₀ one = 0)
    (hker : ∀ f : C₀, dX₀ f = 0 → ∃ t : K, f = t • one) (evX : C₀ →ₗ[K] K) (hevX : evX one = 1)
    (hcompat : ∀ b b', s₀ b b' ∘ₗ incl b = s₁ b b' ∘ₗ incl b')
    (heq : ∀ g : ∀ b, B₁ b, (∀ b b', s₀ b b' (g b) = s₁ b b' (g b')) →
      ∃ θ : G, ∀ b, g b = incl b θ)
    (b₀ : J) (evY : B₁ b₀ →ₗ[K] G) (hevY : evY ∘ₗ incl b₀ = LinearMap.id)
    (c₁₀ : ∀ b, C₁ ⊗[K] B₁ b) (c₀₁ : ∀ b b', C₀ ⊗[K] B₂ b b')
    (hE20 : ∀ b, rTensor (B₁ b) dX₁ (c₁₀ b) = 0)
    (hE11 : ∀ b b', lTensor C₁ (s₁ b b') (c₁₀ b') - lTensor C₁ (s₀ b b') (c₁₀ b) =
      rTensor (B₂ b b') dX₀ (c₀₁ b b'))
    (hfaceX : ∃ eX : C₀ ⊗[K] G, lTensor C₁ evY (c₁₀ b₀) = rTensor G dX₀ eX)
    (hfaceY : ∃ eY : ∀ b, B₁ b, ∀ b b',
      TensorProduct.lid K (B₂ b b') (rTensor (B₂ b b') evX (c₀₁ b b')) =
        s₁ b b' (eY b') - s₀ b b' (eY b)) :
    ∃ e : ∀ b, C₀ ⊗[K] B₁ b, (∀ b, c₁₀ b = rTensor (B₁ b) dX₀ (e b)) ∧
      ∀ b b', c₀₁ b b' = lTensor C₀ (s₁ b b') (e b') - lTensor C₀ (s₀ b b') (e b) := by
  classical
  obtain ⟨eY, heY⟩ := hfaceY
  choose f hf using
    exists_eq_rTensor_of_face hdd hcompat heq b₀ evY hevY c₁₀ c₀₁ hE20 hE11 hfaceX
  set c' : ∀ b b', C₀ ⊗[K] B₂ b b' := fun b b' =>
    c₀₁ b b' - (lTensor C₀ (s₁ b b') (f b') - lTensor C₀ (s₀ b b') (f b)) with hc'
  have hc'ker : ∀ b b', rTensor (B₂ b b') dX₀ (c' b b') = 0 := by
    intro b b'
    rw [hc', map_sub, ← hE11, map_sub, rTensor_lTensor_apply, rTensor_lTensor_apply,
      ← hf, ← hf, sub_self]
  choose g hgg using fun b b' =>
    exists_eq_one_tmul_of_rTensor_eq_zero hone hker _ (c' b b') (hc'ker b b')
  set h' : ∀ b, B₁ b := fun b => eY b - TensorProduct.lid K (B₁ b) (rTensor (B₁ b) evX (f b))
    with hh'
  have hgcob : ∀ b b', g b b' = s₁ b b' (h' b') - s₀ b b' (h' b) := by
    intro b b'
    have h1 : TensorProduct.lid K (B₂ b b') (rTensor (B₂ b b') evX (c' b b')) = g b b' := by
      rw [hgg]
      simp [hevX]
    rw [← h1, hc', map_sub, map_sub, heY, map_sub, map_sub, lid_rTensor_lTensor_apply,
      lid_rTensor_lTensor_apply, hh', map_sub, map_sub]
    abel
  refine ⟨fun b => f b + one ⊗ₜ h' b, fun b => ?_, fun b b' => ?_⟩
  · rw [map_add, rTensor_tmul, hone, zero_tmul, add_zero, hf]
  · have := hgg b b'
    rw [hc', sub_eq_iff_eq_add] at this
    rw [this, hgcob, map_add, map_add, lTensor_tmul, lTensor_tmul, tmul_sub]
    abel

end Main

end Stacks.DoubleCech

end
