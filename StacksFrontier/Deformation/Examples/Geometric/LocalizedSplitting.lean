module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.Deformation.SquareZero.Problem

/-!
# Splitting the conormal differential after localization

Let `B` be an essentially of finite type algebra over `k` and let `P` be a presentation of `B`
over `k` with formally smooth polynomial ring. At a prime `q` of `B` at which `B` is smooth over
`k`, the localized conormal sequence

`0 → (I/I²)_q → (P.CotangentSpace)_q → (Ω_{B/k})_q → 0`

is split exact: the localized Kähler differentials are free and the localized first Koszul
homology vanishes, so the conormal differential admits a retraction over `B_q`.

Such a retraction is defined only after inverting the elements outside `q`. When the conormal
module is finite and the cotangent space finitely presented, the denominators can be cleared:
some `s ∉ q` admits a genuine `B`-linear map whose composite with the conormal differential is
multiplication by `s`.

## Main results

* `Deformation.Examples.exists_smul_id_factor_of_localized_split`: a retraction defined after
  localization yields, after clearing denominators, a map whose composite with the original
  differential is a scalar multiple of the identity.
* `Deformation.Examples.exists_localized_cotangent_retraction_of_isSmoothAt`: at a smooth prime
  the localized conormal differential admits a retraction.
-/

@[expose] public section

namespace Deformation.Examples

/-- A localized retraction can be cleared of denominators when its source is finitely presented
and its target is finite. -/
theorem exists_smul_id_factor_of_localized_split
    {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module R P] [Module.Finite R M] [Module.FinitePresentation R P]
    (d : M →ₗ[R] P) (S : Submonoid R)
    (t : LocalizedModule S P →ₗ[R] LocalizedModule S M)
    (ht : t.comp ((LocalizedModule.map S d).restrictScalars R) = LinearMap.id) :
    ∃ s : S, ∃ l : P →ₗ[R] M, l.comp d = (s : R) • LinearMap.id := by
  obtain ⟨l, s, hl⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (LocalizedModule.mkLinearMap S M) (t.comp (LocalizedModule.mkLinearMap S P))
  have hld : (LocalizedModule.mkLinearMap S M).comp (l.comp d) =
      (LocalizedModule.mkLinearMap S M).comp ((s : R) • LinearMap.id) := by
    ext x
    have h : (LocalizedModule.mkLinearMap S M) (l (d x)) =
        (s : R) • t (LocalizedModule.mkLinearMap S P (d x)) :=
      DFunLike.congr_fun hl (d x)
    have ht' : t (LocalizedModule.mkLinearMap S P (d x)) =
        LocalizedModule.mkLinearMap S M x := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply,
        LocalizedModule.mkLinearMap_apply, LinearMap.restrictScalars_apply,
        LocalizedModule.map_mk] using DFunLike.congr_fun ht (LocalizedModule.mkLinearMap S M x)
    change (LocalizedModule.mkLinearMap S M) (l (d x)) =
      (LocalizedModule.mkLinearMap S M) ((s : R) • x)
    rw [h, ht', map_smul]
  obtain ⟨a, ha⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
    (LocalizedModule.mkLinearMap S M) (l.comp d) ((s : R) • LinearMap.id) hld
  refine ⟨a * s, (a : R) • l, ?_⟩
  simpa only [LinearMap.smul_comp, Submonoid.coe_mul, Submonoid.smul_def, smul_smul] using ha

/-- At a smooth prime the localized conormal sequence is split exact on the left. -/
theorem exists_localized_cotangent_retraction_of_isSmoothAt
    {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [Algebra.EssFiniteType k B]
    (P : Algebra.Extension k B) [Algebra.FormallySmooth k P.Ring]
    (q : PrimeSpectrum B) (hq : Algebra.IsSmoothAt k q.asIdeal) :
    ∃ t : LocalizedModule q.asIdeal.primeCompl P.CotangentSpace →ₗ[B]
        LocalizedModule q.asIdeal.primeCompl P.Cotangent,
      t.comp ((LocalizedModule.map q.asIdeal.primeCompl P.cotangentComplex).restrictScalars B) =
        LinearMap.id := by
  let T := q.asIdeal.primeCompl
  have hq' : q ∈ (Module.support B (Algebra.H1Cotangent k B))ᶜ ∩
      Module.freeLocus B (KaehlerDifferential k B) := by
    rwa [← Algebra.smoothLocus_eq_compl_support_inter]
  have hk : q ∉ Module.support B P.H1Cotangent := by
    rw [P.equivH1CotangentOfFormallySmooth.support_eq]
    exact hq'.1
  have : Subsingleton (LocalizedModule T (LinearMap.ker P.cotangentComplex)) :=
    Module.notMem_support_iff.mp hk
  let f := LocalizedModule.mkLinearMap T P.Cotangent
  let g := LocalizedModule.mkLinearMap T P.CotangentSpace
  let d := IsLocalizedModule.map T f g P.cotangentComplex
  let j := LinearMap.toKerIsLocalized T f g P.cotangentComplex
  let : IsLocalizedModule T j :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization T) T f g P.cotangentComplex
  have : Subsingleton (LinearMap.ker d) :=
    (IsLocalizedModule.iso T j).subsingleton_congr.mp inferInstance
  have hd : Function.Injective d := LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton
  have : Module.Free (Localization T) (LocalizedModule T (KaehlerDifferential k B)) :=
    Module.mem_freeLocus.mp hq'.2
  let d' := LocalizedModule.map T P.cotangentComplex
  let p' := LocalizedModule.map T P.toKaehler
  have he : Function.Exact d' p' :=
    LocalizedModule.map_exact T P.cotangentComplex P.toKaehler
      P.exact_cotangentComplex_toKaehler
  have htfae := @Function.Exact.split_tfae' (Localization T)
    (LocalizedModule T P.Cotangent) (LocalizedModule T P.CotangentSpace)
    (LocalizedModule T (KaehlerDifferential k B)) _ _ _ _ _ _ _ d' p' he
  have hsplit : ∃ t, p'.comp t = LinearMap.id :=
    Module.projective_lifting_property p' LinearMap.id
      (LocalizedModule.map_surjective T P.toKaehler P.toKaehler_surjective)
  obtain ⟨t, ht⟩ := ((htfae.out 1 2 rfl rfl).mp ⟨hd, hsplit⟩).2
  exact ⟨t.restrictScalars B, by ext x; exact DFunLike.congr_fun ht x⟩

/-! ### Compatible extensions of a square-zero extension problem -/

section
open Stacks.Deformation

/-- The identified kernel of an extension is a module over the middle ring through
multiplication by any lift. -/
public theorem kernelEquiv_smul_toB
    {P : SquareZeroExtensionProblem} (X : P.CompatibleExtension)
    (c : X.B') (n : P.N) :
    (X.kernelEquiv (X.toB c • n) : X.B') = c * (X.kernelEquiv n : X.B') :=
  congrArg Subtype.val ((X.kernelEquiv.map_smul (X.toB c) n).trans
    (X.toB_smul_kernel c (X.kernelEquiv n)))

/-- Every element of the kernel of `toB` comes from `N` through the kernel identification. -/
private theorem exists_kernelEquiv_eq_of_toB_eq_zero
    {P : SquareZeroExtensionProblem} (X : P.CompatibleExtension) {x : X.B'} (hx : X.toB x = 0) :
    ∃ n : P.N, (X.kernelEquiv n : X.B') = x :=
  (X.kernelEquiv.surjective ⟨x, hx⟩).imp fun _ h => congrArg Subtype.val h

/-- A map of extensions inducing the identity on `B` and on `N` is an isomorphism. -/
public theorem isomorphic_of_compatibleAlgHom
    {P : SquareZeroExtensionProblem} (X Y : P.CompatibleExtension)
    (f : X.B' →ₐ[P.A'] Y.B') (hq : Y.toB.comp f = X.toB)
    (hn : ∀ n : P.N, f (X.kernelEquiv n) = (Y.kernelEquiv n : Y.B')) :
    SquareZeroExtensionProblem.CompatibleExtension.Isomorphic X Y := by
  have hq_apply (x : X.B') : Y.toB (f x) = X.toB x := DFunLike.congr_fun hq x
  have hbij : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).mpr fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨n, hx'⟩ :=
        exists_kernelEquiv_eq_of_toB_eq_zero X (by rw [← hq_apply, hx, map_zero])
      have hn0 : n = 0 := Y.kernelEquiv.injective <| Subtype.ext <| by
        rw [← hn, hx', hx, map_zero, Submodule.coe_zero]
      rw [← hx', hn0, map_zero, Submodule.coe_zero]
    · obtain ⟨x, hx⟩ := X.surjective (Y.toB y)
      obtain ⟨n, hy⟩ := exists_kernelEquiv_eq_of_toB_eq_zero Y
        (x := y - f x) (by rw [map_sub, hq_apply, hx, sub_self])
      refine ⟨x + (X.kernelEquiv n : X.B'), ?_⟩
      rw [map_add, hn, hy, add_sub_cancel]
  exact ⟨⟨AlgEquiv.ofBijective f hbij, hq, hn⟩⟩

end

end Deformation.Examples

end
