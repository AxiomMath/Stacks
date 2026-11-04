module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import StacksFrontier.RingTheory.FinitePresentation.Relative
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Transport of finite presentation

Lemmas about `Module.FinitePresentation` that do not involve the relative notion: descent along
a surjective ring map composed with a module structure, transport across ring isomorphisms and
semilinear additive isomorphisms, restriction of scalars of finite modules along a surjection,
two-out-of-three in short exact sequences, direct summands, and invariance of finite
presentation under a finite, finitely presented ring map.
-/

open scoped TensorProduct

universe u

/-- Descent of finite presentation along a composite: if `p : S → T` is surjective and the
`U`-module `N`, viewed over `S` via `g.comp p`, is finitely presented, then `N` viewed over `T`
via `g : T → U` is finitely presented.

This complements `Module.finitePresentation_of_compHom`, which descends to the ambient module
structure instead of to a `Module.compHom` one. -/
theorem Module.finitePresentation_of_compHom_comp {S T U N : Type*} [CommRing S] [CommRing T]
    [CommRing U] [AddCommGroup N] [Module U N] (g : T →+* U) (p : S →+* T)
    (hp : Function.Surjective p)
    (h : @Module.FinitePresentation S N _ _ (Module.compHom N (g.comp p))) :
    @Module.FinitePresentation T N _ _ (Module.compHom N g) := by
  let _ : Module T N := Module.compHom N g
  exact Module.finitePresentation_of_compHom p hp h

/-- Spanning transfers along a surjective ring map when the actions agree through it. -/
private theorem span_eq_top_of_smul_eq {A B N : Type*} [Ring A] [Ring B] [AddCommGroup N]
    [Module A N] [Module B N] (f : A →+* B) (hf : Function.Surjective f)
    (hsmul : ∀ (a : A) (n : N), a • n = f a • n) {T : Set N} (h : Submodule.span B T = ⊤) :
    Submodule.span A T = ⊤ := by
  refine eq_top_iff.2 fun n _ => ?_
  have hn : n ∈ Submodule.span B T := h ▸ Submodule.mem_top
  clear ‹n ∈ ⊤›
  induction hn using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul b x _ hx =>
    obtain ⟨a, rfl⟩ := hf b
    exact hsmul a x ▸ Submodule.smul_mem _ a hx

/-- The relations of a finite family transport along a ring isomorphism when the actions agree
through it. -/
private theorem fg_ker_linearCombination_of_smul_eq {A B N : Type*} [Ring A] [Ring B]
    [AddCommGroup N] [Module A N] [Module B N] (e : A ≃+* B)
    (hsmul : ∀ (a : A) (n : N), a • n = e a • n) {s : Set N}
    (hker : (LinearMap.ker (Finsupp.linearCombination A (Subtype.val : s → N))).FG) :
    (LinearMap.ker (Finsupp.linearCombination B (Subtype.val : s → N))).FG := by
  let σ := (e : A →+* B)
  let ip1 : RingHomInvPair σ (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
  let ip2 : RingHomInvPair (e.symm : B →+* A) σ := RingHomInvPair.of_ringEquiv e.symm
  have : RingHomSurjective σ := ⟨e.surjective⟩
  let emE : A ≃ₛₗ[σ] B := { (σ : A →+* B).toSemilinearMap with
    invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv }
  let FE : (s →₀ A) ≃ₛₗ[σ] (s →₀ B) := Finsupp.mapRange.linearEquiv emE
  have hcomm : ∀ c : (s →₀ A),
      Finsupp.linearCombination B (Subtype.val : s → N) (FE c) =
        Finsupp.linearCombination A (Subtype.val : s → N) c := by
    intro c
    simp only [FE, Finsupp.mapRange.linearEquiv_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_mapRange_index (by simp)]
    exact Finsupp.sum_congr fun i _ => (hsmul _ _).symm
  have hmapeq : Submodule.map (FE : (s →₀ A) →ₛₗ[σ] (s →₀ B))
        (LinearMap.ker (Finsupp.linearCombination A (Subtype.val : s → N))) =
      LinearMap.ker (Finsupp.linearCombination B (Subtype.val : s → N)) := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      simp only [LinearMap.mem_ker, LinearEquiv.coe_coe] at hc ⊢
      rwa [hcomm]
    · intro y hy
      refine ⟨FE.symm y, ?_, by simp⟩
      rwa [SetLike.mem_coe, LinearMap.mem_ker, ← hcomm, FE.apply_symm_apply]
  rw [← hmapeq]
  exact Submodule.FG.map (FE : (s →₀ A) →ₛₗ[σ] (s →₀ B)) hker

/-- **Transport of finite presentation across a ring isomorphism.** If `e : S ≃+* S'`
is an isomorphism of (commutative) rings, `N` is an `S`-module, `N'` is an `S'`-module,
and `φ : N ≃+ N'` is an additive isomorphism that is *semilinear* along `e`
(i.e. `φ (s • x) = e s • φ x`), then `N` finitely presented over `S` implies `N'`
finitely presented over `S'`.

Viewing `N'` as an `S`-module by restriction of scalars along `e` makes `φ` an `S`-linear
equivalence, so `N'` is finitely presented over `S`. A finite spanning set then transports to
`S'` because `e` is surjective (`Submodule.restrictScalars_span`), and the relation module
transports across the `e`-semilinear equivalence `(s →₀ S) ≃ₛₗ[e] (s →₀ S')` of coordinate
modules. -/
theorem finitePresentation_of_ringEquiv
    (S S' : Type*) [CommRing S] [CommRing S'] (e : S ≃+* S')
    (N : Type*) [AddCommGroup N] [Module S N]
    (N' : Type*) [AddCommGroup N'] [Module S' N']
    (φ : N ≃+ N') (hφ : ∀ (s : S) (x : N), φ (s • x) = e s • φ x)
    (h : Module.FinitePresentation S N) :
    Module.FinitePresentation S' N' := by
  let mS : Module S N' := Module.compHom N' (e : S →+* S')
  have hFP_S : Module.FinitePresentation S N' :=
    .of_equiv (M := N) { φ with map_smul' := hφ }
  obtain ⟨s, hspan, hker⟩ := hFP_S.out
  refine ⟨s, span_eq_top_of_smul_eq (e.symm : S' →+* S) e.symm.surjective
    (fun a n => ?_) hspan, fg_ker_linearCombination_of_smul_eq e (fun _ _ => rfl) hker⟩
  change a • n = e (e.symm a) • n
  rw [e.apply_symm_apply]

/-- Restriction of scalars along a ring isomorphism preserves finite presentation: if `X` is a
finitely presented `T`-module and `e : S ≃+* T`, then `X` viewed over `S` via `e` is finitely
presented. This is `finitePresentation_of_ringEquiv` with the underlying additive group fixed. -/
theorem fp_transport {S T X : Type*} [CommRing S] [CommRing T]
    [AddCommGroup X] [Module T X] (e : S ≃+* T) [Module.FinitePresentation T X] :
    @Module.FinitePresentation S X _ _ (Module.compHom X (e : S →+* T)) :=
  @finitePresentation_of_ringEquiv T S _ _ e.symm X _ _ X _
    (Module.compHom X (e : S →+* T)) (AddEquiv.refl X)
    (fun t x => by
      show (t • x : X) = e (e.symm t) • x
      rw [e.apply_symm_apply])
    inferInstance

/-- Restriction of scalars along a surjective ring hom preserves `Module.Finite`. -/
theorem finite_restrict {S S' M : Type*} [CommRing S] [CommRing S'] [AddCommGroup M]
    (β : S' →+* S) (hβ : Function.Surjective β) [Module S M]
    [hfin : Module.Finite S M] :
    @Module.Finite S' M _ _ (Module.compHom M β) := by
  let _ : Module S' M := Module.compHom M β
  obtain ⟨T, hT⟩ := hfin.fg_top
  exact ⟨T, span_eq_top_of_smul_eq β hβ (fun _ _ => rfl) hT⟩

/-- **Two-out-of-three for finite presentation over a fixed ring.**
Let `S` be a commutative ring and `0 → N' →[f] N →[g] N'' → 0` a short exact sequence of
`S`-modules. If `N'` and `N''` are finitely presented `S`-modules, then so is `N`.

This is part (2) of Stacks 0519: `ker g = range f ≅ N'` is finitely presented and
`N / ker g ≅ N''` is finitely presented, so `Module.finitePresentation_of_ker` applies to `g`. -/
theorem fp_two_of_three
    {S : Type u} [CommRing S]
    {N' N N'' : Type u} [AddCommGroup N'] [Module S N']
    [AddCommGroup N] [Module S N] [AddCommGroup N''] [Module S N'']
    (f : N' →ₗ[S] N) (g : N →ₗ[S] N'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g)
    [Module.FinitePresentation S N'] [Module.FinitePresentation S N''] :
    Module.FinitePresentation S N := by
  have : Module.FinitePresentation S (LinearMap.ker g) :=
    .of_equiv ((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hex))
  exact Module.finitePresentation_of_ker g hg

/-- A direct summand of a finitely presented module is finitely presented:
if `M × M'` is finitely presented over `S`, then `M` is. -/
theorem Module.FinitePresentation.fst {S : Type*} [CommRing S] {M M' : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    [Module.FinitePresentation S (M × M')] : Module.FinitePresentation S M := by
  refine Module.finitePresentation_of_split_exact (LinearMap.inl S M M')
    (LinearMap.snd S M M') (LinearMap.inr S M M') ?_ ?_ ?_
  · ext m
    simp
  · exact LinearMap.inl_injective
  · rw [LinearMap.exact_iff]
    ext x
    simp [LinearMap.mem_ker, LinearMap.mem_range, Prod.ext_iff, eq_comm]

/-- A direct summand of a finitely presented module is finitely presented:
if `M × M'` is finitely presented over `S`, then `M'` is. -/
theorem Module.FinitePresentation.snd {S : Type*} [CommRing S] {M M' : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
    [Module.FinitePresentation S (M × M')] : Module.FinitePresentation S M' := by
  have : Module.FinitePresentation S (M' × M) := .of_equiv (LinearEquiv.prodComm S M M')
  exact Module.FinitePresentation.fst (M := M') (M' := M)

/-- **Stacks Tag 0564.** Let `P → Q` be a ring map that is
both *finite* (`Q` is module-finite over `P`) and *finitely presented as an
algebra*. Let `M` be a `Q`-module (with `[IsScalarTower P Q M]` forcing the
`P`-module structure to be restriction of scalars along `P → Q`). Then `M` is a
finitely presented `P`-module iff it is a finitely presented `Q`-module.

Descent: `Q` module-finite over `P` makes `M` finite over `Q`, and the kernel of a finite free
`Q`-presentation of `M` is `P`-finitely generated because `M` is `P`-finitely presented, hence
`Q`-finitely generated. Ascent: a map that is finite and finitely presented as an algebra is
finitely presented as a module, so `Module.FinitePresentation.trans` applies. -/
@[ega "IV 1.4.7" "necessity"]
theorem fp_iff_of_finite_fp_algebra
    (P Q : Type*) [CommRing P] [CommRing Q] [Algebra P Q]
    (M : Type*) [AddCommGroup M] [Module P M] [Module Q M] [IsScalarTower P Q M]
    (hfin : Module.Finite P Q) (hfp : Algebra.FinitePresentation P Q) :
    Module.FinitePresentation P M ↔ Module.FinitePresentation Q M := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Module.Finite Q M := Module.Finite.of_restrictScalars_finite P Q M
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Q) (M := M)
    set l : (Fin n → Q) →ₗ[Q] M := Fintype.linearCombination Q s with hl
    have hsurj : Function.Surjective l := by
      rw [← LinearMap.range_eq_top, hl, Fintype.range_linearCombination, hs]
    have hker : (l.ker.restrictScalars P).FG :=
      Module.FinitePresentation.fg_ker (l.restrictScalars P) hsurj
    exact Module.finitePresentation_of_free_of_surjective l hsurj (hker.of_restrictScalars P)
  · have : Module.FinitePresentation P Q :=
      (Module.FinitePresentation.iff_finitePresentation_of_finite P Q).mpr hfp
    exact Module.FinitePresentation.trans P M Q

/-- **Finite presentation descends along a bijective ring map.**  If the action of `R` on `N` is
the action of `R'` read through a *bijective* ring map `f : R →+* R'`, then `N` is a finitely
presented `R`-module as soon as it is a finitely presented `R'`-module.

This is the finite-presentation companion of `Stacks.Module.finite_of_surjective_of_smul_eq`, and
`Function.Surjective f` does **not** suffice in its place.  A surjection supplies a finite
*generating* set over `R` — a spanning set over `R'` spans over `R` because every `R'`-scalar is
`f` of an `R`-scalar, which is the whole of the finiteness statement — but the relations among
that set over `R` are the relations over `R'` *together with* `RingHom.ker f`, so they are
finitely generated only when that kernel is.  Taking `R = ℤ[x₁, x₂, …]`, `R' = ℤ`, `f` the
evaluation at zero and `N = ℤ`, the module `N` is finitely presented over `R'` while over `R` it
is `R / RingHom.ker f` with `RingHom.ker f` not finitely generated, so it is not.  Bijectivity is
the case `RingHom.ker f = ⊥`, and it is what the identifications of sections along a continuous
functor supply.

Only `Ring` is asked of `R` and `R'`: the hypothesis is used through the `f`-semilinear additive
bijection `Finsupp.mapRange` of the coefficient modules, which transports the module of relations,
and not through any `Algebra` structure.  This matters because the rings this is applied to are
the sections of a sheaf of rings on a site, which carry no commutativity instance. -/
theorem Stacks.Module.finitePresentation_of_bijective_of_smul_eq {R R' : Type*} [Ring R]
    [Ring R'] {N : Type*} [AddCommGroup N] [Module R N] [Module R' N] (f : R →+* R')
    (hf : Function.Bijective f) (hsmul : ∀ (r : R) (n : N), r • n = f r • n)
    (hfp : Module.FinitePresentation R' N) : Module.FinitePresentation R N := by
  obtain ⟨s, hspan, hker⟩ := hfp.out
  refine ⟨s, span_eq_top_of_smul_eq f hf.2 hsmul hspan,
    fg_ker_linearCombination_of_smul_eq (RingEquiv.ofBijective f hf).symm (fun a n => ?_) hker⟩
  rw [hsmul]
  congr 1
  exact ((RingEquiv.ofBijective f hf).apply_symm_apply a).symm
