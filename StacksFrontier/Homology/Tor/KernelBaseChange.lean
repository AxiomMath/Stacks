module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe

/-!
# Base change of the kernel of a two-term complex under `Tor` vanishing

Let `N₁ --d--> N₀` be a map of `B`-modules with `N₀` projective and cokernel `H`, and let `C` be
a `B`-module.  If `Tor₁^B(H, C) = 0` and `Tor₂^B(H, C) = 0`, then
`Ker(d) ⊗_B C → Ker(d ⊗_B C)` is an isomorphism, that is
`C ⊗_B Ker(d) = Ker(C ⊗_B N₁ → C ⊗_B N₀)`.  This is the homological algebra of the final
assertion of Stacks 00S2, whose proof runs as follows: writing `M ⊆ N₀` for the image of `d`,
`Tor₁^B(H, C) = 0` makes `0 → M ⊗ C → N₀ ⊗ C → H ⊗ C → 0` exact, and since `N₀` is free,
`Tor₂^B(H, C) = Tor₁^B(M, C)`, so `Tor₂^B(H, C) = 0` makes
`0 → Ker(d) ⊗ C → N₁ ⊗ C → M ⊗ C → 0` exact.

`Tor` here is Mathlib's `CategoryTheory.Tor'`, which left-derives `- ⊗_B C` in the first variable,
so `((Tor' (ModuleCat B) i).obj H).obj C` is `Tor_i^B(H, C)` computed from a projective
resolution of `H`, with the long exact sequence in `H` that the source's proof uses.

## Main results

* `LinearMap.lTensor_injective_of_exact_of_projective`: if `0 → K' → F' → Q → 0` is exact with
  `F'` projective and `C ⊗ K' → C ⊗ F'` injective, then `C ⊗ K → C ⊗ E` is injective for every
  short exact `0 → K → E → Q → 0`, the modules `K` and `E` being in any universe.
* `LinearMap.lTensor_injective_of_retract_of_exact_of_projective`: the same for a retract `Q` of
  such a `Q'`.
* `LinearMap.lTensor_injective_of_isZero_tor'_one`: `Tor₁^B(Q, C) = 0` makes `C ⊗ K → C ⊗ E`
  injective for a short exact `0 → K → E → Q → 0`.
* `LinearMap.isZero_tor'_one_of_isZero_tor'_two`: the dimension shift
  `Tor₂^B(Q, C) = 0 ⇒ Tor₁^B(K, C) = 0` for `0 → K → E → Q → 0` with `E` projective.
* `LinearMap.lTensor_ker_subtype_injective_and_range_eq_of_isZero_tor'`: the statement above.

## Implementation notes

The modules `N₁` and `N₀` of the application (the conormal module and the cotangent space of a
presentation) live in a larger universe than `B`, `C` and `H`, while Mathlib's `Tor` is only
defined in the universe of the ring.  So `Tor` is applied only to modules in that universe: a
free resolution `G → F → H` of `H` is chosen there, the two vanishing hypotheses become the
injectivity of `C ⊗ Ker(F → H) → C ⊗ F` and of `C ⊗ Ker(G → Ker(F → H)) → C ⊗ G`, and these
are carried over to `N₁ → N₀` by universe-polymorphic comparison arguments
(`LinearMap.lTensor_injective_of_exact_of_projective` and its retract form, the latter applied
through Schanuel's comparison of `M` with `Ker(F → H) × N₀`).

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), the final assertion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Function TensorProduct

universe u

namespace LinearMap

section Elementwise

variable {R : Type*} [CommRing R] (T : Type*) [AddCommGroup T] [Module R T]

/-- Tensoring the inclusion `M → M × N` is injective: it has the left inverse `C ⊗ fst`. -/
theorem lTensor_inl_injective (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] : Injective ((LinearMap.inl R M N).lTensor T) := by
  intro x y hxy
  have h := congrArg ((LinearMap.fst R M N).lTensor T) hxy
  rwa [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, LinearMap.fst_comp_inl,
    LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.id_apply] at h

/-- **Comparison of two short exact sequences with the same cokernel.**  Let
`0 → K' → F' → Q → 0` be exact with `F'` projective and with `C ⊗ K' → C ⊗ F'` injective.  Then
for every short exact sequence `0 → K → E → Q → 0`, the map `C ⊗ K → C ⊗ E` is injective.

This is the vanishing of `Tor₁(Q, C)` read off one projective presentation and transported to an
arbitrary one: a lift `F' → E` makes `K' → K × F' → E → 0` exact, and tensoring with `C` keeps
it right exact. -/
theorem lTensor_injective_of_exact_of_projective {K' F' Q : Type*} [AddCommGroup K'] [Module R K']
    [AddCommGroup F'] [Module R F'] [Module.Projective R F'] [AddCommGroup Q] [Module R Q]
    {ι' : K' →ₗ[R] F'} {f' : F' →ₗ[R] Q} (h' : Exact ι' f') (hf' : Surjective f')
    (hT : Injective (ι'.lTensor T))
    {K E : Type*} [AddCommGroup K] [Module R K] [AddCommGroup E] [Module R E]
    {ι : K →ₗ[R] E} {g : E →ₗ[R] Q} (hι : Injective ι) (h : Exact ι g) (hg : Surjective g) :
    Injective (ι.lTensor T) := by
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property g f' hg
  have hgφ : ∀ y, g (φ y) = f' y := fun y => LinearMap.congr_fun hφ y
  have hmem : ∀ z, (φ ∘ₗ ι') z ∈ LinearMap.range ι := fun z =>
    (h _).1 (by rw [LinearMap.comp_apply, hgφ, h'.apply_apply_eq_zero])
  let ψ : K' →ₗ[R] K := (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
    (φ ∘ₗ ι').codRestrict (LinearMap.range ι) hmem
  have hψ : ∀ z, ι (ψ z) = φ (ι' z) := fun z => by
    simp [ψ]
  let u : K' →ₗ[R] K × F' := LinearMap.prod ψ (-ι')
  let v : K × F' →ₗ[R] E := LinearMap.coprod ι φ
  have huv : Exact u v := by
    rintro ⟨k, y⟩
    change ι k + φ y = 0 ↔ ∃ z, u z = (k, y)
    constructor
    · intro hky
      have hy : f' y = 0 := by
        have := congrArg g hky
        rwa [map_add, h.apply_apply_eq_zero, zero_add, hgφ, map_zero] at this
      obtain ⟨z, rfl⟩ := (h' y).1 hy
      refine ⟨-z, Prod.ext ?_ ?_⟩
      · change ψ (-z) = k
        apply hι
        rw [map_neg, map_neg, hψ, eq_comm, eq_neg_iff_add_eq_zero]
        exact hky
      · change (-ι') (-z) = ι' z
        rw [LinearMap.neg_apply, map_neg, neg_neg]
    · rintro ⟨z, hz⟩
      obtain rfl : ψ z = k := congrArg Prod.fst hz
      obtain rfl : (-ι') z = y := congrArg Prod.snd hz
      rw [hψ, LinearMap.neg_apply, map_neg, add_neg_cancel]
  have hv : Surjective v := fun e => by
    obtain ⟨y, hy⟩ := hf' (g e)
    obtain ⟨k, hk⟩ := (h (e - φ y)).1 (by rw [map_sub, hgφ, hy, sub_self])
    exact ⟨(k, y), by simp [v, hk]⟩
  have huvT := lTensor_exact T huv hv
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  set w := (LinearMap.inl R K F').lTensor T x with hw
  have hvw : v.lTensor T w = 0 := by
    rw [hw, ← LinearMap.lTensor_comp_apply, LinearMap.coprod_inl]
    exact hx
  obtain ⟨y, hy⟩ := (huvT w).1 hvw
  have hy0 : y = 0 := by
    have h2 := congrArg ((LinearMap.snd R K F').lTensor T) hy
    rw [← LinearMap.lTensor_comp_apply, LinearMap.snd_prod, hw, ← LinearMap.lTensor_comp_apply,
      LinearMap.snd_comp_inl, LinearMap.lTensor_zero, LinearMap.zero_apply,
      LinearMap.lTensor_neg, LinearMap.neg_apply, neg_eq_zero] at h2
    exact hT (h2.trans (map_zero _).symm)
  have hw0 : w = 0 := by rw [← hy, hy0, map_zero]
  exact lTensor_inl_injective T K F' (hw0.trans (map_zero _).symm)

/-- **The retract form of `LinearMap.lTensor_injective_of_exact_of_projective`.**  Let
`0 → K' → F' → Q' → 0` be exact with `F'` projective and with `C ⊗ K' → C ⊗ F'` injective, and
let `Q` be a retract of `Q'`.  Then for every short exact sequence `0 → K → E → Q → 0`, the map
`C ⊗ K → C ⊗ E` is injective.  Indeed `0 → K → E × Ker(Q' → Q) → Q' → 0` is short exact. -/
theorem lTensor_injective_of_retract_of_exact_of_projective {K' F' Q' Q : Type*}
    [AddCommGroup K'] [Module R K'] [AddCommGroup F'] [Module R F'] [Module.Projective R F']
    [AddCommGroup Q'] [Module R Q'] [AddCommGroup Q] [Module R Q]
    {ι' : K' →ₗ[R] F'} {f' : F' →ₗ[R] Q'} (h' : Exact ι' f') (hf' : Surjective f')
    (hT : Injective (ι'.lTensor T)) (a : Q →ₗ[R] Q') (b : Q' →ₗ[R] Q)
    (hab : b ∘ₗ a = LinearMap.id)
    {K E : Type*} [AddCommGroup K] [Module R K] [AddCommGroup E] [Module R E]
    {ι : K →ₗ[R] E} {g : E →ₗ[R] Q} (hι : Injective ι) (h : Exact ι g) (hg : Surjective g) :
    Injective (ι.lTensor T) := by
  have hba : ∀ q, b (a q) = q := fun q => LinearMap.congr_fun hab q
  let C := LinearMap.ker b
  let g'' : E × C →ₗ[R] Q' := LinearMap.coprod (a ∘ₗ g) C.subtype
  let ι'' : K →ₗ[R] E × C := LinearMap.inl R E C ∘ₗ ι
  have hι'' : Injective ι'' := fun x y hxy => hι (congrArg Prod.fst hxy)
  have h'' : Exact ι'' g'' := by
    rintro ⟨e, c⟩
    change a (g e) + (c : Q') = 0 ↔ ∃ k, ι'' k = (e, c)
    constructor
    · intro hec
      have hge : g e = 0 := by
        have := congrArg b hec
        rwa [map_add, hba, LinearMap.mem_ker.1 c.2, add_zero, map_zero] at this
      obtain ⟨k, hk⟩ := (h e).1 hge
      refine ⟨k, Prod.ext hk ?_⟩
      rw [hge, map_zero, zero_add] at hec
      exact (Subtype.ext hec).symm
    · rintro ⟨k, hk⟩
      obtain rfl : ι k = e := congrArg Prod.fst hk
      obtain rfl : (0 : C) = c := congrArg Prod.snd hk
      rw [h.apply_apply_eq_zero, map_zero, zero_add, ZeroMemClass.coe_zero]
  have hg'' : Surjective g'' := fun q => by
    obtain ⟨e, he⟩ := hg (b q)
    have hc : q - a (b q) ∈ C := by
      rw [LinearMap.mem_ker, map_sub, hba, sub_self]
    exact ⟨(e, ⟨_, hc⟩), by simp [g'', he]⟩
  have hinj := lTensor_injective_of_exact_of_projective T h' hf' hT hι'' h'' hg''
  rw [LinearMap.lTensor_comp, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

end Elementwise

section Tor

variable {S : Type u} [CommRing S] (T : Type u) [AddCommGroup T] [Module S T]

/-- The short exact sequence `0 → K → E → Q → 0` in `ModuleCat S` of an injective map followed by
a surjective map exact at the middle. -/
noncomputable abbrev shortComplexOfExact {K E Q : Type u} [AddCommGroup K] [Module S K]
    [AddCommGroup E] [Module S E] [AddCommGroup Q] [Module S Q] {ι : K →ₗ[S] E}
    {g : E →ₗ[S] Q} (h : Exact ι g) : ShortComplex (ModuleCat.{u} S) :=
  ShortComplex.mk (ModuleCat.ofHom ι) (ModuleCat.ofHom g)
    (by ext x; exact h.apply_apply_eq_zero x)

/-- The sequence `shortComplexOfExact` is short exact. -/
theorem shortExact_shortComplexOfExact {K E Q : Type u} [AddCommGroup K] [Module S K]
    [AddCommGroup E] [Module S E] [AddCommGroup Q] [Module S Q] {ι : K →ₗ[S] E}
    {g : E →ₗ[S] Q} (hι : Injective ι) (h : Exact ι g) (hg : Surjective g) :
    (shortComplexOfExact h).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 h
  mono_f := (ModuleCat.mono_iff_injective _).2 hι
  epi_g := (ModuleCat.epi_iff_surjective _).2 hg

/-- The functor `- ⊗_S T`, whose left derived functors are `Tor'`. -/
noncomputable abbrev tensorRightFunctor : ModuleCat.{u} S ⥤ ModuleCat.{u} S :=
  (tensoringRight (ModuleCat.{u} S)).obj (ModuleCat.of S T)

instance : PreservesFiniteColimits (tensorRightFunctor (S := S) T) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft (ModuleCat.of S T)) :=
    (ihom.adjunction (ModuleCat.of S T)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (tensorLeft (ModuleCat.of S T)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact preservesFiniteColimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of S T))

/-- **`Tor₁ = 0` gives injectivity.**  For a short exact sequence `0 → K → E → Q → 0` of
`S`-modules, if `Tor₁^S(Q, T) = 0` then `T ⊗_S K → T ⊗_S E` is injective. -/
theorem lTensor_injective_of_isZero_tor'_one {K E Q : Type u} [AddCommGroup K] [Module S K]
    [AddCommGroup E] [Module S E] [AddCommGroup Q] [Module S Q] {ι : K →ₗ[S] E}
    {g : E →ₗ[S] Q} (hι : Injective ι) (h : Exact ι g) (hg : Surjective g)
    (hTor : IsZero (((Tor' (ModuleCat.{u} S) 1).obj (ModuleCat.of S Q)).obj
      (ModuleCat.of S T))) :
    Injective (ι.lTensor T) := by
  have hS := shortExact_shortComplexOfExact hι h hg
  let F := tensorRightFunctor (S := S) T
  have hex := F.leftDerived_exact_δ₂ hS 0
  have hz : IsZero ((F.leftDerived (0 + 1)).obj (shortComplexOfExact h).X₃) := hTor
  have hmono : Mono ((F.leftDerived 0).map (shortComplexOfExact h).f) :=
    hex.mono_g (hz.eq_of_src _ _)
  have heq : F.map (shortComplexOfExact h).f =
      F.leftDerivedZeroIsoSelf.inv.app _ ≫ (F.leftDerived 0).map (shortComplexOfExact h).f ≫
        F.leftDerivedZeroIsoSelf.hom.app _ := by
    rw [F.leftDerivedZeroIsoSelf.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hFmono : Mono (F.map (shortComplexOfExact h).f) := by
    rw [heq]
    infer_instance
  rw [LinearMap.lTensor_inj_iff_rTensor_inj]
  exact (ModuleCat.mono_iff_injective _).1 hFmono

/-- **Dimension shifting for `Tor`.**  For a short exact sequence `0 → K → E → Q → 0` of
`S`-modules with `E` projective, `Tor₂^S(Q, T) = 0` implies `Tor₁^S(K, T) = 0`. -/
theorem isZero_tor'_one_of_isZero_tor'_two {K E Q : Type u} [AddCommGroup K] [Module S K]
    [AddCommGroup E] [Module S E] [Module.Projective S E] [AddCommGroup Q] [Module S Q]
    {ι : K →ₗ[S] E} {g : E →ₗ[S] Q} (hι : Injective ι) (h : Exact ι g) (hg : Surjective g)
    (hTor : IsZero (((Tor' (ModuleCat.{u} S) 2).obj (ModuleCat.of S Q)).obj
      (ModuleCat.of S T))) :
    IsZero (((Tor' (ModuleCat.{u} S) 1).obj (ModuleCat.of S K)).obj (ModuleCat.of S T)) := by
  have hS := shortExact_shortComplexOfExact hι h hg
  let F := tensorRightFunctor (S := S) T
  have hex := F.leftDerived_exact_δ₂ hS 1
  have hz₃ : IsZero ((F.leftDerived (1 + 1)).obj (shortComplexOfExact h).X₃) := hTor
  have hz₂ : IsZero ((F.leftDerived 1).obj (shortComplexOfExact h).X₂) :=
    isZero_Tor'_succ_of_projective (ModuleCat.{u} S) (ModuleCat.of S E) (ModuleCat.of S T) 0
  exact hex.isZero_X₂ (hz₃.eq_of_src _ _) (hz₂.eq_of_tgt _ _)

/-- **Base change of the kernel of a two-term complex under `Tor` vanishing** (the homological
algebra of the final assertion of Stacks 00S2).  Let `d : N₁ → N₀` and `p : N₀ → Q` be maps of
`S`-modules with `N₁ → N₀ → Q → 0` exact and `N₀` projective, and let `T` be an `S`-module with
`Tor₁^S(Q, T) = 0` and `Tor₂^S(Q, T) = 0`.  Then `T ⊗_S Ker(d) → T ⊗_S N₁` is injective with
image `Ker(T ⊗_S N₁ → T ⊗_S N₀)`, so `T ⊗_S Ker(d) = Ker(T ⊗_S d)`.

The modules `N₁` and `N₀` may live in any universe; only `Q` and `T` are in the universe of
`S`, where `Tor` is defined. -/
theorem lTensor_ker_subtype_injective_and_range_eq_of_isZero_tor' {N₁ N₀ : Type*}
    [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₀] [Module S N₀] [Module.Projective S N₀]
    {Q : Type u} [AddCommGroup Q] [Module S Q] (d : N₁ →ₗ[S] N₀) (p : N₀ →ₗ[S] Q)
    (hdp : Exact d p) (hp : Surjective p)
    (h₁ : IsZero (((Tor' (ModuleCat.{u} S) 1).obj (ModuleCat.of S Q)).obj (ModuleCat.of S T)))
    (h₂ : IsZero (((Tor' (ModuleCat.{u} S) 2).obj (ModuleCat.of S Q)).obj (ModuleCat.of S T))) :
    Injective ((LinearMap.ker d).subtype.lTensor T) ∧
      LinearMap.range ((LinearMap.ker d).subtype.lTensor T) = LinearMap.ker (d.lTensor T) := by
  -- A free resolution `G → F → Q` in the universe of `S`.
  let q : (Q →₀ S) →ₗ[S] Q := Finsupp.linearCombination S (_root_.id : Q → Q)
  have hq : Surjective q := fun x => ⟨Finsupp.single x (1 : S), by simp [q]⟩
  let K₀ := LinearMap.ker q
  let e : (K₀ →₀ S) →ₗ[S] K₀ := Finsupp.linearCombination S (_root_.id : K₀ → K₀)
  have he : Surjective e := fun x => ⟨Finsupp.single x (1 : S), by simp [e]⟩
  have hA : Injective (K₀.subtype.lTensor T) :=
    lTensor_injective_of_isZero_tor'_one T K₀.injective_subtype (LinearMap.exact_subtype_ker_map q)
      hq h₁
  have hK₀ : IsZero (((Tor' (ModuleCat.{u} S) 1).obj (ModuleCat.of S K₀)).obj
      (ModuleCat.of S T)) :=
    isZero_tor'_one_of_isZero_tor'_two T K₀.injective_subtype (LinearMap.exact_subtype_ker_map q)
      hq h₂
  have hB : Injective ((LinearMap.ker e).subtype.lTensor T) :=
    lTensor_injective_of_isZero_tor'_one T (LinearMap.ker e).injective_subtype
      (LinearMap.exact_subtype_ker_map e) he hK₀
  -- `M = Ker(p) = Im(d)` and the surjection `d' : N₁ → M`.
  let M := LinearMap.ker p
  have hi : Injective (M.subtype.lTensor T) :=
    lTensor_injective_of_exact_of_projective T (LinearMap.exact_subtype_ker_map q) hq hA
      M.injective_subtype (LinearMap.exact_subtype_ker_map p) hp
  let d' : N₁ →ₗ[S] M := d.codRestrict M fun x => hdp.apply_apply_eq_zero x
  have hd' : Surjective d' := fun m => by
    obtain ⟨x, hx⟩ := (hdp m).1 m.2
    exact ⟨x, Subtype.ext hx⟩
  have hexd' : Exact (LinearMap.ker d).subtype d' := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    exact Subtype.ext_iff
  -- `M` is a retract of `K₀ × N₀` (Schanuel), which has the presentation `G × N₀ → K₀ × N₀`.
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property q p hq
  obtain ⟨α, hα⟩ := Module.projective_lifting_property p q hp
  have hqβ : ∀ x, q (β x) = p x := fun x => LinearMap.congr_fun hβ x
  have hpα : ∀ y, p (α y) = q y := fun y => LinearMap.congr_fun hα y
  let a : M →ₗ[S] K₀ × N₀ := LinearMap.prod
    ((β ∘ₗ M.subtype).codRestrict K₀ fun m => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hqβ]; exact m.2)
    M.subtype
  let b₀ : K₀ × N₀ →ₗ[S] N₀ := LinearMap.coprod (α ∘ₗ K₀.subtype) (LinearMap.id - α ∘ₗ β)
  let b : K₀ × N₀ →ₗ[S] M := b₀.codRestrict M fun kx => by
    rw [LinearMap.mem_ker]
    simp only [b₀, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.coe_subtype,
      LinearMap.sub_apply, LinearMap.id_apply, map_add, map_sub, hpα, hqβ,
      LinearMap.mem_ker.1 kx.1.2, zero_add, sub_self]
  have hab : b ∘ₗ a = LinearMap.id := by
    ext m
    simp [a, b, b₀]
  let f' : (K₀ →₀ S) × N₀ →ₗ[S] K₀ × N₀ := e.prodMap LinearMap.id
  let ι' : LinearMap.ker e →ₗ[S] (K₀ →₀ S) × N₀ :=
    LinearMap.inl S (K₀ →₀ S) N₀ ∘ₗ (LinearMap.ker e).subtype
  have h' : Exact ι' f' := by
    rintro ⟨y, x⟩
    change (e y, x) = 0 ↔ ∃ z, ι' z = (y, x)
    constructor
    · intro hyx
      have hy : e y = 0 := congrArg Prod.fst hyx
      obtain rfl : x = 0 := congrArg Prod.snd hyx
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨z, hz⟩
      obtain rfl : (z : K₀ →₀ S) = y := congrArg Prod.fst hz
      obtain rfl : (0 : N₀) = x := congrArg Prod.snd hz
      exact Prod.ext z.2 rfl
  have hf' : Surjective f' := fun ⟨k, x⟩ => by
    obtain ⟨y, hy⟩ := he k
    exact ⟨(y, x), by simp [f', hy]⟩
  have hT' : Injective (ι'.lTensor T) := by
    rw [LinearMap.lTensor_comp, LinearMap.coe_comp]
    exact (lTensor_inl_injective T _ _).comp hB
  have hii : Injective ((LinearMap.ker d).subtype.lTensor T) :=
    lTensor_injective_of_retract_of_exact_of_projective T h' hf' hT' a b hab
      (LinearMap.ker d).injective_subtype hexd' hd'
  refine ⟨hii, ?_⟩
  have hd : d.lTensor T = M.subtype.lTensor T ∘ₗ d'.lTensor T := by
    rw [← LinearMap.lTensor_comp]
    rfl
  rw [hd, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 hi)]
  exact (lTensor_exact T hexd' hd').linearMap_ker_eq.symm

end Tor

end LinearMap

end
