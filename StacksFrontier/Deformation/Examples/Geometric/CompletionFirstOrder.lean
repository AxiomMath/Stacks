module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Noetherian.OfPrime
public import Mathlib.RingTheory.Smooth.Locus
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.Deformation.Examples.Geometric.LocalizedSplitting
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensionMaps
public import StacksFrontier.Deformation.TangentSpace.SquareZero
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.HomCompletion
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe
public import StacksFrontier.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.Quotient
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.Deformation.Examples.Geometric.Completion
public import StacksFrontier.RingTheory.Branches.Completion

/-!
# First-order extensions and adic completion

Let `k` be a field, let `B` be a finite type `k`-algebra, let `J ⊆ B` be an ideal outside whose
zero set `B` is smooth over `k`, and let `N` be a finite `B`-module. Completion along `J` is a
bijection from the square-zero extensions of `B` by `N`, up to isomorphism, to those of `B^` by
`N^`.

The source's proof shows that two canonical comparison maps on the first Ext group of the naive
cotangent complex are bijective: `Stacks.Deformation.naiveCotangentExtOneMap` along `N → N^`
and `Stacks.Deformation.naiveCotangentExtOneTowerMap` along `B → B^`. Together with the
classification of **Stacks 0GPT** and the criterion of **Stacks 0GPV** for the existence of a
map between two square-zero extensions, their bijectivity gives the completion bijection in the
form that pins it down: a class and its image are exactly the pairs of extensions admitting a
`k`-algebra map between their middle rings over `B → B^` and over `N → N^`.

Both are proved bijective here, in
`Deformation.Examples.bijective_naiveCotangentExtOneMap_adicCompletion` and
`Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_adicCompletion`.

## Main results

* `Deformation.Examples.bijective_naiveCotangentExtOneMap_adicCompletion`: the comparison map
  `Ext¹_B(NL_{B/k}, N) → Ext¹_B(NL_{B/k}, N^)` is bijective.
* `Deformation.Examples.bijective_naiveCotangentExtOneTowerMap_adicCompletion`: the comparison
  map `Ext¹_{B^}(NL_{B^/k}, N^) → Ext¹_B(NL_{B/k}, N^)` is bijective; its two halves are
  `Deformation.Examples.injective_naiveCotangentExtOneTowerMap_adicCompletion` and
  `Deformation.Examples.surjective_naiveCotangentExtOneTowerMap_adicCompletion`.
* `Deformation.Examples.exists_squareZeroAlgebraExtensionClassesCompletionEquiv`: the
  completion bijection on isomorphism classes of square-zero extensions, characterised by the
  existence of a compatible map of middle rings.
* `Deformation.Examples.exists_compatible_algebraMap_splitAlgebraExtension_adicCompletion`: the
  two split extensions are related by such a compatible map, so the characterisation above
  constrains the bijection on at least one class.

## Implementation notes

`Exal_k(B, N)` is the isomorphism classes of `Stacks.Deformation.algebraExtensionProblem`, as in
`StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder`, and the completions are
Mathlib's `AdicCompletion`. Canonicity is expressed through **Stacks 0GPV** rather than by
exhibiting the completed extension: the source's map sends an extension `C` to its completion,
which does admit a `k`-algebra map `C → C^` over `B → B^` and over `N → N^`, and the stated
characterisation says the bijection matches precisely such pairs.

`Stacks.Deformation.extOneCokernel`, which presents `Ext¹_B(NL_{B/k}, N)`, is built on the
canonical presentation `Algebra.Generators.self k B`, whose conormal module is not finite. The
argument therefore runs at a finite presentation and is transported along
`Deformation.Examples.conormalCokernelEquiv`, and it is driven by the fact that at a finite
presentation the conormal differential splits after inverting any element of `J`, so a power of
`J` annihilates the conormal cokernel with every coefficient module. Both of those live in
`StacksFrontier.Deformation.SquareZero.ConormalTorsion`, which the henselization statements use
too. What is added here is the comparison along `N → N^`, which given the splitting is the
statement that `Hom_B(C, N^)` is the `J`-adic completion of `Hom_B(C, N)`.

## References

* [Stacks Project, Tag 0DZ4](https://stacks.math.columbia.edu/tag/0DZ4)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 0GPV](https://stacks.math.columbia.edu/tag/0GPV)
-/

@[expose] public section

universe uk uB uN uC uw uw' uw'' v

namespace Deformation.Examples

open Stacks.Deformation


/-! ### Completing the coefficients of a module of homomorphisms -/

section HomCompletion

variable {A : Type uk} {M : Type uB} {N : Type uN} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- `AdicCompletion.homCompletionEquiv` with the three types in independent universes: for
finite modules over a Noetherian ring, completing `Hom_A(M, N)` gives the `A`-linear maps from
`M` into the completion of `N`, and the completion of `f` is `f` followed by `N → N^`. -/
private theorem exists_homAdicCompletionEquiv (I : Ideal A) :
    ∃ e : AdicCompletion I (M →ₗ[A] N) ≃ₗ[A] (M →ₗ[A] AdicCompletion I N),
      ∀ f : M →ₗ[A] N,
        e (AdicCompletion.of I (M →ₗ[A] N) f) = (AdicCompletion.of I N).comp f := by
  let : Small.{uk} M := Module.Finite.small A M
  let : Small.{uk} N := Module.Finite.small A N
  let : SMul A (Shrink.{uk} M) := (Shrink.addEquiv (α := M)).smul A
  let : Module A (Shrink.{uk} M) := inferInstance
  let : SMul A (Shrink.{uk} N) := (Shrink.addEquiv (α := N)).smul A
  let : Module A (Shrink.{uk} N) := inferInstance
  let : SMulCommClass A A (Shrink.{uk} N) := ⟨fun a b n ↦
    ((mul_smul a b n).symm.trans (congrArg (· • n) (mul_comm a b))).trans (mul_smul b a n)⟩
  let : IsScalarTower A A (Shrink.{uk} N) := ⟨fun a b n ↦ by
    rw [smul_eq_mul]; exact mul_smul a b n⟩
  let eM : Shrink.{uk} M ≃ₗ[A] M := Shrink.linearEquiv A M
  let eN : Shrink.{uk} N ≃ₗ[A] N := Shrink.linearEquiv A N
  let eH : (Shrink.{uk} M →ₗ[A] Shrink.{uk} N) ≃ₗ[A] (M →ₗ[A] N) :=
    LinearEquiv.arrowCongr (σ₁₁' := RingHom.id A) (σ₂₂' := RingHom.id A) eM eN
  refine ⟨((AdicCompletion.congr I eH).symm.restrictScalars A).trans
    ((AdicCompletion.homCompletionEquiv I).trans
      (LinearEquiv.arrowCongr (σ₁₁' := RingHom.id A) (σ₂₂' := RingHom.id A) eM
        ((AdicCompletion.congr I eN).restrictScalars A))), fun f ↦ ?_⟩
  refine LinearMap.ext fun m ↦ ?_
  have h1 : (AdicCompletion.congr I eH).symm (AdicCompletion.of I (M →ₗ[A] N) f) =
      AdicCompletion.of I (Shrink.{uk} M →ₗ[A] Shrink.{uk} N) (eH.symm f) := by
    simp [AdicCompletion.congr, AdicCompletion.map_of]
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1,
    LinearEquiv.arrowCongr_apply, AdicCompletion.homCompletionEquiv_of_apply,
    LinearMap.comp_apply]
  have h2 : (AdicCompletion.congr I eN) (AdicCompletion.of I (Shrink.{uk} N)
      (eH.symm f (eM.symm m))) = AdicCompletion.of I N (eN (eH.symm f (eM.symm m))) := by
    simp [AdicCompletion.congr, AdicCompletion.map_of]
  rw [h2]
  congr 1
  change eN (eN.symm (f (eM (eM.symm m)))) = f m
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Every `A`-linear map into the completion of `N` agrees, to any prescribed `I`-adic order,
with the completion of an `A`-linear map into `N`. -/
private theorem exists_sub_mem_pow_smul_top {I : Ideal A} (hI : I.FG) (n : ℕ)
    (g : M →ₗ[A] AdicCompletion I N) :
    ∃ f : M →ₗ[A] N, g - (AdicCompletion.of I N).comp f ∈
      I ^ n • (⊤ : Submodule A (M →ₗ[A] AdicCompletion I N)) := by
  obtain ⟨e, he⟩ := exists_homAdicCompletionEquiv (M := M) (N := N) I
  obtain ⟨c, hc⟩ := e.surjective g
  obtain ⟨f, hf⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A (M →ₗ[A] N)))
    (AdicCompletion.eval I (M →ₗ[A] N) n c)
  refine ⟨f, ?_⟩
  have hker : c - AdicCompletion.of I (M →ₗ[A] N) f ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I (M →ₗ[A] N))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    change AdicCompletion.eval I (M →ₗ[A] N) n (c - AdicCompletion.of I (M →ₗ[A] N) f) = 0
    rw [map_sub, AdicCompletion.eval_of, ← hf, Submodule.mkQ_apply, sub_self]
  have hmem := Submodule.smul_top_le_comap_smul_top (I ^ n) e.toLinearMap hker
  rwa [Submodule.mem_comap, LinearEquiv.coe_coe, map_sub, hc, he f] at hmem

/-- Conversely, a map into `N` whose completion is `I`-adically small is itself small. -/
private theorem mem_pow_smul_top_of_of_comp_mem {I : Ideal A} (hI : I.FG) (n : ℕ)
    (f : M →ₗ[A] N)
    (hf : (AdicCompletion.of I N).comp f ∈
      I ^ n • (⊤ : Submodule A (M →ₗ[A] AdicCompletion I N))) :
    f ∈ I ^ n • (⊤ : Submodule A (M →ₗ[A] N)) := by
  obtain ⟨e, he⟩ := exists_homAdicCompletionEquiv (M := M) (N := N) I
  have hback := Submodule.smul_top_le_comap_smul_top (I ^ n) e.symm.toLinearMap hf
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, ← he f, LinearEquiv.symm_apply_apply,
    AdicCompletion.pow_smul_top_eq_ker_eval hI] at hback
  change AdicCompletion.eval I (M →ₗ[A] N) n (AdicCompletion.of I (M →ₗ[A] N) f) = 0 at hback
  rw [AdicCompletion.eval_of] at hback
  exact (Submodule.Quotient.mk_eq_zero _).1 hback

end HomCompletion

/-! ### Bijectivity of the comparison map along `N → N^` -/

section Comparison

/-- At a finite presentation whose conormal differential is split by a power of `J`, completing
the coefficients is a bijection on the conormal cokernel. -/
private theorem bijective_conormalCokernelPushAt_adicCompletion
    (k : Type uk) (B : Type uB) [CommRing k] [CommRing B] [Algebra k B]
    [IsNoetherianRing B] [Algebra.EssFiniteType k B]
    (P : Algebra.Extension.{uw} k B) [Algebra.FormallySmooth k P.Ring]
    [Module.Finite B P.Cotangent] [Module.Finite B P.CotangentSpace]
    [Module.FinitePresentation B P.CotangentSpace]
    (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    Function.Bijective (conormalCokernelPushAt P (AdicCompletion.of J N)) := by
  obtain ⟨n, hn⟩ := exists_pow_le_conormalSplittingIdeal P J hsm
  have hJ : J.FG := IsNoetherian.noetherian _
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, conormalCokernelPushAt_mk,
      Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨l, hl⟩ := hx
    obtain ⟨t, ht⟩ := exists_sub_mem_pow_smul_top (A := B) (M := P.CotangentSpace) (N := N)
      hJ n l
    have h3 := Submodule.smul_top_le_comap_smul_top (J ^ n)
      (LinearMap.lcomp B (AdicCompletion J N) P.cotangentComplex) ht
    rw [Submodule.mem_comap] at h3
    have heq : LinearMap.lcomp B (AdicCompletion J N) P.cotangentComplex
        (l - (AdicCompletion.of J N).comp t) =
        (AdicCompletion.of J N).comp (f - t.comp P.cotangentComplex) := by
      refine LinearMap.ext fun y ↦ ?_
      have hly : l (P.cotangentComplex y) = AdicCompletion.of J N (f y) :=
        DFunLike.congr_fun hl y
      simp [hly]
    rw [heq] at h3
    have h4 := mem_pow_smul_top_of_of_comp_mem (A := B) (M := P.Cotangent) (N := N) hJ n _ h3
    have h5 := smul_top_le_range_lcomp P hn N h4
    have h6 : t.comp P.cotangentComplex ∈
        LinearMap.range (LinearMap.lcomp B N P.cotangentComplex) := ⟨t, rfl⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simpa using Submodule.add_mem _ h5 h6
  · intro y
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨f, hf⟩ := exists_sub_mem_pow_smul_top (A := B) (M := P.Cotangent) (N := N) hJ n g
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    rw [conormalCokernelPushAt_mk, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    have h2 := Submodule.neg_mem _ (smul_top_le_range_lcomp P hn (AdicCompletion J N) hf)
    rwa [neg_sub] at h2

/-- **Stacks 0DZ4**, first half of the proof.  For a finite type algebra `B` over a field `k`
which is smooth over `k` outside the zero set of an ideal `J`, and a finite `B`-module `N`, the
canonical comparison map `Ext¹_B(NL_{B/k}, N) → Ext¹_B(NL_{B/k}, N^)` along `N → N^` is
bijective.

The argument is the source's: `Ext¹_B(NL_{B/k}, N)` is annihilated by a power of `J`, because
the conormal differential of a finite presentation splits after inverting any element outside
the non-smooth locus, and the comparison map is then the completion map of a module of
homomorphisms between finite modules. -/
public theorem bijective_naiveCotangentExtOneMap_adicCompletion
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    Function.Bijective (naiveCotangentExtOneMap k B (AdicCompletion.of J N)) := by
  let : Algebra.FinitePresentation k B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let P₀ := Algebra.Presentation.ofFinitePresentation k B
  let Q := P₀.reindex (Equiv.ulift.{uB}) (Equiv.refl _)
  let : Module.Finite B Q.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite Q.fg_ker
  let : Module.Finite B Q.toExtension.CotangentSpace :=
    Module.Finite.of_basis Q.toGenerators.cotangentSpaceBasis
  let : Module.FinitePresentation B Q.toExtension.CotangentSpace :=
    Module.finitePresentation_of_projective B Q.toExtension.CotangentSpace
  let : Algebra.FormallySmooth k Q.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth k (MvPolynomial _ k))
  have hQ := bijective_conormalCokernelPushAt_adicCompletion k B Q.toExtension J hsm N
  have hself : Function.Bijective (conormalCokernelPushAt
      (Algebra.Generators.self k B).toExtension (AdicCompletion.of J N)) :=
    (bijective_conormalCokernelPushAt_iff
      (Algebra.Generators.defaultHom (Algebra.Generators.self k B)
        Q.toGenerators).toExtensionHom
      (Algebra.Generators.defaultHom Q.toGenerators
        (Algebra.Generators.self k B)).toExtensionHom
      (AdicCompletion.of J N)).2 hQ
  have hpush : (conormalCokernelPush k B (AdicCompletion.of J N) : _ → _) =
      (conormalCokernelPushAt (Algebra.Generators.self k B).toExtension
        (AdicCompletion.of J N) : _ → _) := by
    funext x
    obtain ⟨δ, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl
  have hb : Function.Bijective (conormalCokernelPush k B (AdicCompletion.of J N)) := by
    rw [hpush]; exact hself
  have hfun : (naiveCotangentExtOneMap k B (AdicCompletion.of J N) : _ → _) =
      (extCokernelIso k B (AdicCompletion J N)).symm ∘
        (conormalCokernelPush k B (AdicCompletion.of J N)) ∘
        (extCokernelIso k B N) := rfl
  rw [hfun]
  exact ((extCokernelIso k B (AdicCompletion J N)).symm.bijective.comp hb).comp
    (extCokernelIso k B N).bijective

end Comparison

/-! ### Bijectivity of the comparison map along `B → B^` -/

section Tower
/-- Adic completeness transported along a ring isomorphism. -/
private theorem isAdicComplete_of_ringEquiv {R : Type uw} {S : Type uw'} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete (I.map (e : R →+* S)) S := by
  let : Algebra R S := (e : R →+* S).toAlgebra
  let : IsScalarTower R S S := IsScalarTower.right
  let el : R ≃ₗ[R] S :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun r x => map_mul e r x
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  exact (IsAdicComplete.map_algebraMap_iff (I := I) (S := S) (M := S)).mpr
    (Stacks.Examples.isAdicComplete_of_linearEquiv el.symm ‹IsAdicComplete I R›)


/-- The middle ring of a square-zero extension of a Noetherian ring by a finite module is
itself Noetherian: the kernel is a finitely generated nilpotent ideal. -/
private theorem isNoetherianRing_compatibleExtension
    {S : Stacks.Deformation.SquareZeroExtensionProblem} [IsNoetherianRing S.B]
    [Module.Finite S.B S.N] (Y : S.CompatibleExtension.{v}) :
    IsNoetherianRing Y.B' := by
  obtain ⟨s, hs⟩ := (Module.finite_def.mp inferInstance : (⊤ : Submodule S.B S.N).FG)
  let incl : S.N → Y.B' := fun n => kernelInclusion Y n
  have hzero : incl 0 = 0 := (kernelInclusion Y).map_zero
  have hadd : ∀ x y : S.N, incl (x + y) = incl x + incl y :=
    fun x y => (kernelInclusion Y).map_add x y
  have hker : ∀ n : S.N, Y.toB (incl n) = 0 := fun n => toB_kernelInclusion Y n
  have hsmul : ∀ (b : Y.B') (n : S.N), incl (Y.toB b • n) = b * incl n :=
    fun b n => kernelEquiv_smul_toB Y b n
  have hfg : Submodule.FG (RingHom.ker Y.toB.toRingHom) := by
    rw [Submodule.fg_def]
    refine ⟨incl '' (↑s : Set S.N), (s.finite_toSet).image _, le_antisymm ?_ ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨n, -, rfl⟩
      exact hker n
    · intro z hz
      have key : ∀ n ∈ Submodule.span S.B (↑s : Set S.N),
          incl n ∈ Submodule.span Y.B' (incl '' (↑s : Set S.N)) := by
        intro n hn
        induction hn using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => rw [hzero]; exact Submodule.zero_mem _
        | add y w _ _ hy hw => rw [hadd]; exact Submodule.add_mem _ hy hw
        | smul c y _ hy =>
            obtain ⟨b, hb⟩ := Y.surjective c
            rw [← hb, hsmul]
            exact Ideal.mul_mem_left _ b hy
      have hn := key (Y.kernelEquiv.symm ⟨z, hz⟩) (by rw [hs]; exact Submodule.mem_top)
      rwa [show incl (Y.kernelEquiv.symm ⟨z, hz⟩) = z from
        congrArg Subtype.val (Y.kernelEquiv.apply_symm_apply ⟨z, hz⟩)] at hn
  exact isNoetherianRing_of_surjective_fg_nilpotent_ker Y.toB.toRingHom Y.surjective hfg
    ⟨2, by simpa only [Ideal.zero_eq_bot] using Y.sq_zero⟩


/-- A square-zero extension of `C` by `M` admitting an algebra section of its surjection to
`C` is isomorphic to the split extension. -/
private theorem isomorphic_split_of_section
    {A : Type uk} {C : Type uB} [CommRing A] [CommRing C] [Algebra A C]
    {M : Type uN} [AddCommGroup M] [Module C M]
    (Y : (algebraExtensionProblem A C M).CompatibleExtension.{max uB uN})
    (s : C →ₐ[A] Y.B') (hs : ∀ c : C, Y.toB (s c) = c) :
    SquareZeroExtensionProblem.CompatibleExtension.Isomorphic
      (splitAlgebraExtension A C M) Y := by
  let P := splitAlgebraExtension A C M
  let incl : M → Y.B' := fun n => kernelInclusion Y n
  have hz : incl 0 = 0 := (kernelInclusion Y).map_zero
  have ha : ∀ x y : M, incl (x + y) = incl x + incl y :=
    fun x y => (kernelInclusion Y).map_add x y
  have hk : ∀ n : M, Y.toB (incl n) = 0 := fun n => toB_kernelInclusion Y n
  have hm : ∀ n m : M, incl n * incl m = 0 := fun n m =>
    kernelInclusion_mul_kernelInclusion Y n m
  have hsm : ∀ (c : C) (n : M), incl (c • n) = s c * incl n := by
    intro c n
    have h := kernelEquiv_smul_toB Y (s c) n
    rwa [hs c] at h
  let f : P.B' →ₐ[A] Y.B' :=
    { toFun := fun z => s (TrivSqZeroExt.fst z) + incl (TrivSqZeroExt.snd z)
      map_one' := by
        change s (TrivSqZeroExt.fst (1 : P.B')) + incl (TrivSqZeroExt.snd (1 : P.B')) = 1
        rw [show TrivSqZeroExt.fst (1 : P.B') = 1 from rfl,
          show TrivSqZeroExt.snd (1 : P.B') = (0 : M) from rfl, hz, map_one, add_zero]
      map_mul' := fun z w => by
        change s (TrivSqZeroExt.fst (z * w)) + incl (TrivSqZeroExt.snd (z * w))
          = (s (TrivSqZeroExt.fst z) + incl (TrivSqZeroExt.snd z)) *
            (s (TrivSqZeroExt.fst w) + incl (TrivSqZeroExt.snd w))
        have key : (s (TrivSqZeroExt.fst z) + incl (TrivSqZeroExt.snd z)) *
            (s (TrivSqZeroExt.fst w) + incl (TrivSqZeroExt.snd w))
            = s (TrivSqZeroExt.fst z) * s (TrivSqZeroExt.fst w)
              + (s (TrivSqZeroExt.fst z) * incl (TrivSqZeroExt.snd w)
                + s (TrivSqZeroExt.fst w) * incl (TrivSqZeroExt.snd z)) := by
          rw [add_mul, mul_add, mul_add, hm]
          ring
        rw [show TrivSqZeroExt.fst (z * w)
              = TrivSqZeroExt.fst z * TrivSqZeroExt.fst w from rfl,
          show TrivSqZeroExt.snd (z * w)
              = TrivSqZeroExt.fst z • TrivSqZeroExt.snd w
                + TrivSqZeroExt.fst w • TrivSqZeroExt.snd z from rfl,
          map_mul, ha, hsm, hsm, key]
      map_zero' := by
        change s (TrivSqZeroExt.fst (0 : P.B')) + incl (TrivSqZeroExt.snd (0 : P.B')) = 0
        rw [show TrivSqZeroExt.fst (0 : P.B') = (0 : C) from rfl,
          show TrivSqZeroExt.snd (0 : P.B') = (0 : M) from rfl, hz, map_zero, add_zero]
      map_add' := fun z w => by
        change s (TrivSqZeroExt.fst (z + w)) + incl (TrivSqZeroExt.snd (z + w))
          = (s (TrivSqZeroExt.fst z) + incl (TrivSqZeroExt.snd z)) +
            (s (TrivSqZeroExt.fst w) + incl (TrivSqZeroExt.snd w))
        rw [show TrivSqZeroExt.fst (z + w)
              = TrivSqZeroExt.fst z + TrivSqZeroExt.fst w from rfl,
          show TrivSqZeroExt.snd (z + w)
              = TrivSqZeroExt.snd z + TrivSqZeroExt.snd w from rfl, map_add, ha]
        ring
      commutes' := fun a => by
        change s (TrivSqZeroExt.fst (algebraMap A P.B' a))
            + incl (TrivSqZeroExt.snd (algebraMap A P.B' a)) = algebraMap A Y.B' a
        rw [show TrivSqZeroExt.fst (algebraMap A P.B' a) = algebraMap A C a from rfl,
          show TrivSqZeroExt.snd (algebraMap A P.B' a) = (0 : M) from rfl, hz, add_zero,
          AlgHom.commutes] }
  refine isomorphic_of_compatibleAlgHom P Y f ?_ ?_
  · refine AlgHom.ext fun z => ?_
    change Y.toB (s (TrivSqZeroExt.fst z) + incl (TrivSqZeroExt.snd z)) = P.toB z
    rw [map_add, hs, hk]
    exact add_zero _
  · intro n
    refine Eq.trans ?_ (rfl : incl n = (Y.kernelEquiv n : Y.B'))
    change s (0 : C) + incl n = incl n
    rw [map_zero, zero_add]



/-- The canonical `A`-algebra map from `C` into the ring of the split extension. -/
private def splitInl (A : Type uk) (C : Type uB) [CommRing A] [CommRing C] [Algebra A C]
    (M : Type uN) [AddCommGroup M] [Module C M] :
    C →ₐ[A] (splitAlgebraExtension A C M).B' where
  toFun c := (TrivSqZeroExt.inl c : (splitAlgebraExtension A C M).B')
  map_one' := rfl
  map_mul' x y := TrivSqZeroExt.ext rfl (by
    change (0 : M) = x • (0 : M) + y • (0 : M)
    rw [smul_zero, smul_zero, add_zero])
  map_zero' := rfl
  map_add' x y := TrivSqZeroExt.ext rfl (by
    change (0 : M) = (0 : M) + (0 : M)
    rw [add_zero])
  commutes' a := rfl

private theorem toB_splitInl (A : Type uk) (C : Type uB) [CommRing A] [CommRing C] [Algebra A C]
    (M : Type uN) [AddCommGroup M] [Module C M] (c : C) :
    (splitAlgebraExtension A C M).toB (splitInl A C M c) = c := rfl

/-- If `M ⧸ IM` is finite over `A`, then the `I`-adic completion of `M` is a finite module
over the `I`-adic completion of `A`. -/
private theorem module_finite_adicCompletion {A : Type uB} [CommRing A] {I : Ideal A}
    (hI : I.FG) (M : Type uN) [AddCommGroup M] [Module A M]
    (hfin : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := by
  let B := AdicCompletion I A
  let J := I.map (algebraMap A B)
  have : IsPrecomplete J B := (AdicCompletion.isAdicComplete_self I hI).toIsPrecomplete
  have e := AdicCompletion.quotPowSMulTopEquiv hI M 1
  rw [pow_one] at e
  apply Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top J
    (IsHausdorff.map_algebraMap_iff.mpr (AdicCompletion.instIsHausdorff I M)).iInf_pow_smul
  have hres : Module.Finite A
      (AdicCompletion I M ⧸ (J • (⊤ : Submodule B (AdicCompletion I M))).restrictScalars A) := by
    rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
    exact hfin.equiv e.symm
  have : Module.Finite A (AdicCompletion I M ⧸ J • (⊤ : Submodule B (AdicCompletion I M))) :=
    hres.equiv (Submodule.Quotient.restrictScalarsEquiv A _)
  have := Module.Finite.of_restrictScalars_finite A B
    (AdicCompletion I M ⧸ J • (⊤ : Submodule B (AdicCompletion I M)))
  exact Module.Finite.of_restrictScalars_finite B (B ⧸ J) _

/-- The middle ring of a square-zero extension of the completion `B^` by `N^` is complete for
the ideal pulled back from `J B^`: it is complete along its square-zero kernel, and the
quotient `B^` is complete along `J B^`, so **Stacks 0DYC** applies. -/
private theorem isAdicComplete_compatibleExtension_adicCompletion
    (k : Type uk) (B : Type uB) [CommRing k] [CommRing B] [Algebra k B] [IsNoetherianRing B]
    (J : Ideal B) (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N]
    (Y : (algebraExtensionProblem k (AdicCompletion J B)
      (AdicCompletion J N)).CompatibleExtension.{max uB uN})
    (hnoe : IsNoetherianRing Y.B') :
    IsAdicComplete ((J.map (algebraMap B (AdicCompletion J B))).comap Y.toB.toRingHom) Y.B' := by
  have := hnoe
  set K := RingHom.ker Y.toB.toRingHom with hK
  set Jc := J.map (algebraMap B (AdicCompletion J B)) with hJc
  set J' := Jc.comap Y.toB.toRingHom with hJ'
  have hnil : IsNilpotent K := ⟨2, by simpa only [Ideal.zero_eq_bot] using Y.sq_zero⟩
  have hKc : IsAdicComplete K Y.B' := IsAdicComplete.of_isNilpotent K hnil
  have hBc : IsAdicComplete Jc (AdicCompletion J B) :=
    (IsAdicComplete.map_algebraMap_iff (I := J) (S := AdicCompletion J B)
      (M := AdicCompletion J B)).mpr inferInstance
  have := hBc
  let e : (Y.B' ⧸ K) ≃+* AdicCompletion J B :=
    RingHom.quotientKerEquivOfSurjective (f := Y.toB.toRingHom) Y.surjective
  have hq : IsAdicComplete (Jc.map (e.symm : AdicCompletion J B →+* (Y.B' ⧸ K))) (Y.B' ⧸ K) :=
    isAdicComplete_of_ringEquiv e.symm Jc
  have hmapeq : Jc.map (e.symm : AdicCompletion J B →+* (Y.B' ⧸ K))
      = J'.map (algebraMap Y.B' (Y.B' ⧸ K)) := by
    have h1 : Jc.map (e.symm : AdicCompletion J B →+* (Y.B' ⧸ K)) = Jc.comap (e : _ →+* _) :=
      Ideal.map_symm e
    have h2 : J'.map (algebraMap Y.B' (Y.B' ⧸ K)) = Jc.comap (e : _ →+* _) := by
      have h3 : J' = (Jc.comap (e : _ →+* _)).comap (Ideal.Quotient.mk K) := by
        rw [hJ', Ideal.comap_comap]
        rfl
      rw [h3]
      exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective _
    rw [h1, h2]
  rw [hmapeq] at hq
  exact IsAdicComplete.of_quotient K J'
    ((IsAdicComplete.map_algebraMap_iff (I := J') (S := Y.B' ⧸ K) (M := Y.B' ⧸ K)).mp hq)

/-- **Stacks 0DZ4**, injectivity of the comparison map along `B → B^`.  For a Noetherian ring
`B`, an ideal `J` and a finite `B`-module `N`, the canonical map
`Ext¹_{B^}(NL_{B^/k}, N^) → Ext¹_B(NL_{B/k}, N^)` is injective.

The argument is the source's: a class whose restriction along `B → B^` vanishes is, by
**Stacks 0GPV**, represented by a square-zero extension `0 → N^ → Y → B^ → 0` whose middle ring
receives a `k`-algebra map from `B` splitting it over `B`.  The middle ring is Noetherian and
`J`-adically complete (**Stacks 0DYC**, applied to its square-zero kernel), so that map extends
to `B^` and is a section of `Y → B^`; a section splits the extension, so the class is zero. -/
public theorem injective_naiveCotangentExtOneTowerMap_adicCompletion
    (k : Type uk) (B : Type uB) [CommRing k] [CommRing B] [Algebra k B] [IsNoetherianRing B]
    (J : Ideal B) (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    Function.Injective (naiveCotangentExtOneTowerMap k B (AdicCompletion J B)
      (N := AdicCompletion J N)) := by
  have hfin : Module.Finite (AdicCompletion J B) (AdicCompletion J N) :=
    module_finite_adicCompletion (IsNoetherian.noetherian J) N inferInstance
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro ζ hζ
  let eC := squareZeroAlgebraExtensionClassesEquivExtOne k (AdicCompletion J B)
    (AdicCompletion J N)
  obtain ⟨Y, hY⟩ := Quotient.exists_rep (eC.symm ζ)
  have hYζ : eC ⟦Y⟧ = ζ := by rw [hY]; exact eC.apply_symm_apply ζ
  -- `Y` restricted along `B → B^` is the split extension, so there is a section over `B`
  obtain ⟨hmap, hmapB, -⟩ :=
    (exists_compatible_algebraMap_iff k B (AdicCompletion J B)
      (LinearMap.id : AdicCompletion J N →ₗ[B] AdicCompletion J N)
      (splitAlgebraExtension k B (AdicCompletion J N)) Y).mpr (by
        rw [squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, hYζ, hζ, map_zero])
  let σ : B →ₐ[k] Y.B' := hmap.comp (splitInl k B (AdicCompletion J N))
  have hσ : ∀ b : B, Y.toB (σ b) = algebraMap B (AdicCompletion J B) b := by
    intro b
    have h := hmapB (splitInl k B (AdicCompletion J N) b)
    rwa [toB_splitInl] at h
  -- the middle ring is Noetherian and `J`-adically complete, so the section extends
  have hnoe : IsNoetherianRing Y.B' := by
    have h1 : IsNoetherianRing
        ((algebraExtensionProblem k (AdicCompletion J B) (AdicCompletion J N)).B) :=
      inferInstanceAs (IsNoetherianRing (AdicCompletion J B))
    have h2 : Module.Finite
        ((algebraExtensionProblem k (AdicCompletion J B) (AdicCompletion J N)).B)
        ((algebraExtensionProblem k (AdicCompletion J B) (AdicCompletion J N)).N) := hfin
    exact isNoetherianRing_compatibleExtension Y
  have hcomp := isAdicComplete_compatibleExtension_adicCompletion k B J N Y hnoe
  have hmaple : J.map (σ : B →+* Y.B') ≤
      (J.map (algebraMap B (AdicCompletion J B))).comap Y.toB.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    change Y.toB (σ j) ∈ J.map (algebraMap B (AdicCompletion J B))
    rw [hσ]
    exact Ideal.mem_map_of_mem _ hj
  obtain ⟨σ', hσ'⟩ := exists_algHom_adicCompletion_of_map_le J
    ((J.map (algebraMap B (AdicCompletion J B))).comap Y.toB.toRingHom) σ hmaple
  -- the extension is a section of `Y → B^`
  have hofalg : ∀ p : B, AdicCompletion.of J B p = algebraMap B (AdicCompletion J B) p := by
    intro p
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  let toBk : Y.B' →ₐ[k] AdicCompletion J B := Y.toB
  have hid : ((J ^ 1).map (AlgHom.id k B)) ≤ J := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    rw [pow_one]
    intro x hx
    exact hx
  have hsec : toBk.comp σ' = AlgHom.id k (AdicCompletion J B) := by
    refine AdicCompletion.algHom_ext_of_of k J (IsNoetherian.noetherian J) J
      (AlgHom.id k B) hid _ _ ?_ ?_
    · intro p
      change Y.toB (σ' (AdicCompletion.of J B p)) = AdicCompletion.of J B p
      rw [hofalg, hσ' p, hσ p]
    · intro p
      rfl
  have hs : ∀ z : AdicCompletion J B, Y.toB (σ' z) = z := fun z => AlgHom.congr_fun hsec z
  -- a section splits the extension, so the class is zero
  have hiso := isomorphic_split_of_section Y σ' hs
  rw [← hYζ, ← Quotient.sound hiso, squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero]

end Tower

/-! ### Completing a square-zero extension -/

section Restrict

variable {R : Type uw} [CommRing R] (I : Ideal R) (S : Type uw') [CommRing S] [Algebra R S]
  (M : Type uw'') [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (JS : Ideal S) (hJS : JS = I.map (algebraMap R S))

include hJS in
/-- The level-`n` quotients of the two towers are identified by the identity on classes. The
content is `quotEquivMapPowModule`; this is its spelling for this section's data. -/
private def quotRestrictEquiv (n : ℕ) :
    (M ⧸ (I ^ n • (⊤ : Submodule R M))) ≃ₗ[R] (M ⧸ (JS ^ n • (⊤ : Submodule S M))) :=
  quotEquivMapPowModule I S M hJS n

include hJS in
private theorem quotRestrictEquiv_mk (n : ℕ) (x : M) :
    quotRestrictEquiv I S M JS hJS n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

private theorem transitionMap_quotRestrictEquiv {m n : ℕ} (hmn : m ≤ n)
    (x : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
    AdicCompletion.transitionMap JS M hmn (quotRestrictEquiv I S M JS hJS n x)
      = quotRestrictEquiv I S M JS hJS m (AdicCompletion.transitionMap I M hmn x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- **The two indexings of an adic completion of a module agree.** -/
private def adicCompletionRestrictEquiv : AdicCompletion I M ≃+ AdicCompletion JS M where
  toFun x := ⟨fun n => quotRestrictEquiv I S M JS hJS n (x.val n), fun {m n} hmn =>
    (transitionMap_quotRestrictEquiv I S M JS hJS hmn (x.val n)).trans
      (congrArg (quotRestrictEquiv I S M JS hJS m) (x.property hmn))⟩
  invFun y := ⟨fun n => (quotRestrictEquiv I S M JS hJS n).symm (y.val n), fun {m n} hmn =>
    (quotRestrictEquiv I S M JS hJS m).injective (by
      rw [LinearEquiv.apply_symm_apply, ← transitionMap_quotRestrictEquiv I S M JS hJS hmn,
        LinearEquiv.apply_symm_apply]
      exact y.property hmn)⟩
  left_inv x := Subtype.ext (funext fun n => (quotRestrictEquiv I S M JS hJS n).symm_apply_apply _)
  right_inv y := Subtype.ext (funext fun n => (quotRestrictEquiv I S M JS hJS n).apply_symm_apply _)
  map_add' x y := Subtype.ext (funext fun n => map_add (quotRestrictEquiv I S M JS hJS n) _ _)

private theorem adicCompletionRestrictEquiv_val (x : AdicCompletion I M) (n : ℕ) :
    (adicCompletionRestrictEquiv I S M JS hJS x).val n
      = quotRestrictEquiv I S M JS hJS n (x.val n) := rfl

end Restrict


section Util

/-- Multiplication of classes in a quotient by an ideal. -/
private theorem quotMk_mul {R : Type uw} [CommRing R] (p : Ideal R) (a b : R) :
    Submodule.Quotient.mk (p := p) (a * b)
      = Submodule.Quotient.mk (p := p) a * Submodule.Quotient.mk (p := p) b := rfl

/-- Two elements of an ideal with zero square multiply to zero. -/
private theorem mul_eq_zero_of_sq_eq_bot {R : Type uw} [CommRing R] {I : Ideal R} (h : I ^ 2 = ⊥)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have hm : x * y ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  rwa [h, Ideal.mem_bot] at hm

end Util

section Exactness

variable {C : Type uC} [CommRing C] [IsNoetherianRing C]

/-- Adic completion is exact on the sequence defined by an ideal of a Noetherian ring. -/
private theorem map_subtype_exact (I K : Ideal C) :
    Function.Exact (AdicCompletion.map I K.subtype) (AdicCompletion.map I K.mkQ) :=
  AdicCompletion.map_exact (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)

end Exactness

section Abstract

variable {B : Type uB} {C : Type uC} {N : Type uN}
  [CommRing B] [CommRing C] [AddCommGroup N] [Algebra C B]
  [Module B N] [Module C N] [IsScalarTower C B N]
  (I : Ideal C) (JB : Ideal B) (hIJ : JB = I.map (algebraMap C B))
  (hs : Function.Surjective (algebraMap C B : C → B))

private theorem ker_algebraLinearMap :
    LinearMap.ker (Algebra.linearMap C B) = RingHom.ker (algebraMap C B : C →+* B) := rfl

include hs in
/-- The identification `C ⧸ ker (C → B) ≃ B` of `C`-modules. -/
private noncomputable def quotKerEquiv :
    (C ⧸ RingHom.ker (algebraMap C B : C →+* B)) ≃ₗ[C] B :=
  (Submodule.quotEquivOfEq _ _ (ker_algebraLinearMap (C := C) (B := B)).symm).trans
    (LinearMap.quotKerEquivOfSurjective (Algebra.linearMap C B) hs)

include hs in
private theorem quotKerEquiv_mk (c : C) :
    quotKerEquiv hs (Submodule.Quotient.mk c) = algebraMap C B c := rfl

include hs in
private theorem algebraLinearMap_factor :
    Algebra.linearMap C B
      = (quotKerEquiv hs).toLinearMap ∘ₗ (RingHom.ker (algebraMap C B : C →+* B)).mkQ :=
  LinearMap.ext fun c => (quotKerEquiv_mk hs c).symm

include hIJ in
/-- The map of adic completions induced by `C → B`, as a function. -/
private noncomputable def compFun (x : AdicCompletion I C) : AdicCompletion JB B :=
  adicCompletionRestrictEquiv I B B JB hIJ (AdicCompletion.map I (Algebra.linearMap C B) x)

include hIJ in
private theorem compFun_val_mk (x : AdicCompletion I C) (n : ℕ) (c : C)
    (hc : x.val n = Submodule.Quotient.mk c) :
    (compFun I JB hIJ x).val n =
      Submodule.Quotient.mk (p := (JB ^ n • (⊤ : Submodule B B))) (algebraMap C B c) := by
  rw [compFun, adicCompletionRestrictEquiv_val, AdicCompletion.map_val_apply, hc]
  rfl

include hIJ in
private theorem compFun_of (c : C) :
    compFun I JB hIJ (AdicCompletion.of I C c)
      = AdicCompletion.of JB B (algebraMap C B c) := rfl

include hIJ hs in
private theorem compFun_surjective : Function.Surjective (compFun I JB hIJ) := by
  intro y
  obtain ⟨z, hz⟩ := (adicCompletionRestrictEquiv I B B JB hIJ).surjective y
  obtain ⟨x, hx⟩ := AdicCompletion.map_surjective I (f := Algebra.linearMap C B) hs z
  exact ⟨x, by rw [compFun, hx, hz]⟩

include hIJ in
private theorem compFun_eq_zero_iff (x : AdicCompletion I C) :
    compFun I JB hIJ x = 0 ↔ AdicCompletion.map I (Algebra.linearMap C B) x = 0 := by
  constructor
  · intro h
    exact (adicCompletionRestrictEquiv I B B JB hIJ).injective
      (h.trans (map_zero (adicCompletionRestrictEquiv I B B JB hIJ)).symm)
  · intro h
    rw [compFun, h, map_zero]

include hs in
private theorem map_algebraLinearMap_eq (x : AdicCompletion I C) :
    AdicCompletion.map I (Algebra.linearMap C B) x
      = AdicCompletion.map I (quotKerEquiv hs).toLinearMap
          (AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).mkQ x) := by
  rw [AdicCompletion.map_comp_apply, ← algebraLinearMap_factor hs]

include hs in
private theorem map_mkQ_eq_zero_iff (x : AdicCompletion I C) :
    AdicCompletion.map I (Algebra.linearMap C B) x = 0 ↔
      AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).mkQ x = 0 := by
  rw [map_algebraLinearMap_eq I hs]
  constructor
  · intro h
    refine (AdicCompletion.congr I (quotKerEquiv hs)).injective ?_
    rw [AdicCompletion.congr_apply, AdicCompletion.congr_apply, h, map_zero]
  · intro h
    rw [h, map_zero]

include hIJ in
/-- The identification of the two indexings of the completion of `N` is semilinear for the
completed structure map. -/
private theorem restrictEquiv_smul (c' : AdicCompletion I C) (y : AdicCompletion I N) :
    adicCompletionRestrictEquiv I B N JB hIJ (c' • y)
      = compFun I JB hIJ c' • adicCompletionRestrictEquiv I B N JB hIJ y := by
  refine AdicCompletion.ext fun n => ?_
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (c'.val n)
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
  have hl : Submodule.Quotient.mk (p := (I ^ n • (⊤ : Submodule C C))) c
        • Submodule.Quotient.mk (p := (I ^ n • (⊤ : Submodule C N))) m
      = Submodule.Quotient.mk (p := (I ^ n • (⊤ : Submodule C N))) (c • m) := rfl
  have hr : Submodule.Quotient.mk (p := (JB ^ n • (⊤ : Submodule B B))) (algebraMap C B c)
        • Submodule.Quotient.mk (p := (JB ^ n • (⊤ : Submodule B N))) m
      = Submodule.Quotient.mk (p := (JB ^ n • (⊤ : Submodule B N))) (algebraMap C B c • m) := rfl
  rw [adicCompletionRestrictEquiv_val, AdicCompletion.smul_eval, AdicCompletion.smul_eval,
    compFun_val_mk I JB hIJ c' n c hc.symm, adicCompletionRestrictEquiv_val, ← hc, ← hm, hl]
  simp only [quotRestrictEquiv_mk]
  rw [hr, IsScalarTower.algebraMap_smul]

variable [IsNoetherianRing C]

section WithBase

variable {k : Type uk} [CommRing k] [Algebra k B] [Algebra k C] [IsScalarTower k C B]

include hIJ in
/-- The map of adic completions induced by `C → B`, as a `k`-algebra map. -/
private noncomputable def compAlgHom : AdicCompletion I C →ₐ[k] AdicCompletion JB B where
  toFun := compFun I JB hIJ
  map_one' := by
    refine AdicCompletion.ext fun n => ?_
    rw [compFun_val_mk I JB hIJ 1 n 1 rfl, map_one]
    rfl
  map_mul' x y := by
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
    have hxy : (x * y).val n = Submodule.Quotient.mk (c * d) := by
      rw [AdicCompletion.val_mul, ← hc, ← hd]; rfl
    rw [compFun_val_mk I JB hIJ _ n _ hxy, AdicCompletion.val_mul,
      compFun_val_mk I JB hIJ x n c hc.symm, compFun_val_mk I JB hIJ y n d hd.symm, map_mul]
    rfl
  map_zero' := by
    refine AdicCompletion.ext fun n => ?_
    rw [compFun_val_mk I JB hIJ 0 n 0 rfl, map_zero]
    rfl
  map_add' x y := by
    simp only [compFun, map_add]
  commutes' r := by
    rw [AdicCompletion.algebraMap_apply, compFun_of, AdicCompletion.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply k C B r]

include hIJ hs in
private theorem ker_compAlgHom :
    RingHom.ker (compAlgHom (k := k) I JB hIJ).toRingHom
      = LinearMap.range
          (AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).subtype) := by
  ext x
  rw [RingHom.mem_ker]
  have h1 : (compAlgHom (k := k) I JB hIJ).toRingHom x = compFun I JB hIJ x := rfl
  rw [h1, compFun_eq_zero_iff I JB hIJ, map_mkQ_eq_zero_iff I hs,
    ← LinearMap.mem_ker, (map_subtype_exact I _).linearMap_ker_eq]
  exact Iff.rfl

include hIJ hs in
/-- The kernel of the completed map has square zero. -/
private theorem sq_zero_ker_compAlgHom
    (hK2 : RingHom.ker (algebraMap C B : C →+* B) ^ 2 = ⊥) :
    RingHom.ker (compAlgHom (k := k) I JB hIJ).toRingHom ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.mpr fun u hu v hv => ?_
  rw [ker_compAlgHom (k := k) I JB hIJ hs] at hu hv
  have key : ∀ (z : AdicCompletion I (RingHom.ker (algebraMap C B : C →+* B))) (m : ℕ),
      ∃ w : RingHom.ker (algebraMap C B : C →+* B),
        (AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).subtype z).val m
          = Submodule.Quotient.mk (w : C) := by
    intro z m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
    exact ⟨w, by rw [AdicCompletion.map_val_apply, ← hw]; rfl⟩
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  rw [Ideal.mem_bot]
  refine AdicCompletion.ext fun n => ?_
  obtain ⟨w, hw⟩ := key u' n
  obtain ⟨w', hw'⟩ := key v' n
  rw [AdicCompletion.val_mul, hw, hw', ← quotMk_mul, mul_eq_zero_of_sq_eq_bot hK2 w.2 w'.2]
  simp

include hIJ hs in
/-- **Stacks 0DZ4**, the construction behind the surjectivity half.  The `I`-adic completion of
the middle ring of a square-zero extension `0 → K → C → B → 0` is a square-zero extension of
the completion of `B` by the completion of `N ≃ K`, and the canonical map `C → Ĉ` is
compatible with the two exact rows. -/
private theorem exists_extension_abstract
    (hK2 : RingHom.ker (algebraMap C B : C →+* B) ^ 2 = ⊥)
    (eKN : N ≃ₗ[C] RingHom.ker (algebraMap C B : C →+* B)) :
    ∃ Y : (algebraExtensionProblem k (AdicCompletion JB B)
        (AdicCompletion JB N)).CompatibleExtension.{uC},
      ∃ h : C →ₐ[k] Y.B',
        (∀ z : C, Y.toB (h z) = algebraMap B (AdicCompletion JB B) (algebraMap C B z)) ∧
          ∀ n : N, h ((eKN n : C)) = kernelInclusion Y (AdicCompletion.of JB N n) := by
  classical
  let : IsScalarTower k C (AdicCompletion I C) := IsScalarTower.of_algebraMap_eq' rfl
  let Θ : AdicCompletion I C →ₐ[k] AdicCompletion JB B := compAlgHom I JB hIJ
  have hΘs : Function.Surjective Θ := compFun_surjective I JB hIJ hs
  have hker : RingHom.ker Θ.toRingHom
      = LinearMap.range
          (AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).subtype) :=
    ker_compAlgHom I JB hIJ hs
  have hΘsq : RingHom.ker Θ.toRingHom ^ 2 = ⊥ := sq_zero_ker_compAlgHom I JB hIJ hs hK2
  have hmem : ∀ y : AdicCompletion I C, y ∈ RingHom.ker Θ.toRingHom ↔ Θ y = 0 :=
    fun _ => RingHom.mem_ker
  let smulInst : SMul (AdicCompletion JB B) (RingHom.ker Θ.toRingHom) :=
    ⟨fun d x => ⟨Function.surjInv hΘs d * (x : AdicCompletion I C),
      Ideal.mul_mem_left _ _ x.2⟩⟩
  have hsmul : ∀ (c : AdicCompletion I C) (x : RingHom.ker Θ.toRingHom),
      Θ.toRingHom c • x = c • x := by
    intro c x
    refine Subtype.ext ?_
    have h1 : Θ (Function.surjInv hΘs (Θ c)) = Θ c := Function.surjInv_eq hΘs (Θ c)
    have h2 : Function.surjInv hΘs (Θ c) - c ∈ RingHom.ker Θ.toRingHom := by
      rw [hmem, map_sub, h1, sub_self]
    have h3 := mul_eq_zero_of_sq_eq_bot hΘsq h2 x.2
    rw [sub_mul, sub_eq_zero] at h3
    exact h3
  let modInst : Module (AdicCompletion JB B) (RingHom.ker Θ.toRingHom) :=
    Function.Surjective.moduleLeft Θ.toRingHom hΘs hsmul
  have hiKinj : Function.Injective
      (AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).subtype) :=
    AdicCompletion.map_injective I (Submodule.injective_subtype _)
  let e3 : AdicCompletion I (RingHom.ker (algebraMap C B : C →+* B))
      ≃ₗ[AdicCompletion I C] (RingHom.ker Θ.toRingHom) :=
    (LinearEquiv.ofInjective
      (AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).subtype)
      hiKinj).trans (LinearEquiv.ofEq _ _ hker.symm)
  let rN := adicCompletionRestrictEquiv I B N JB hIJ
  let cKN := AdicCompletion.congr I eKN
  let E : AdicCompletion JB N ≃ₗ[AdicCompletion JB B] (RingHom.ker Θ.toRingHom) :=
    { toFun := fun m => e3 (cKN (rN.symm m))
      invFun := fun x => rN (cKN.symm (e3.symm x))
      map_add' := fun m m' => by simp only [map_add]
      map_smul' := fun β m => by
        obtain ⟨c', rfl⟩ := hΘs β
        have h1 : rN.symm (Θ c' • m) = c' • rN.symm m := by
          refine rN.injective ?_
          rw [AddEquiv.apply_symm_apply, restrictEquiv_smul I JB hIJ c' (rN.symm m),
            AddEquiv.apply_symm_apply]
          rfl
        have h2 : e3 (cKN (rN.symm (Θ c' • m))) = c' • e3 (cKN (rN.symm m)) := by
          rw [h1, map_smul, map_smul]
        exact h2.trans (hsmul c' _).symm
      left_inv := fun m => by
        simp only [LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun x => by
        simp only [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] }
  have hr : ∀ n : N, rN.symm (AdicCompletion.of JB N n) = AdicCompletion.of I N n := by
    intro n
    refine rN.injective ?_
    rw [AddEquiv.apply_symm_apply]
    rfl
  have hgoal : ∀ n : N, AdicCompletion.of I C ((eKN n : C))
      = AdicCompletion.map I (RingHom.ker (algebraMap C B : C →+* B)).subtype
          (cKN (rN.symm (AdicCompletion.of JB N n))) := by
    intro n
    rw [hr n]
    rfl
  dsimp only [algebraExtensionProblem]
  exact ⟨{ B' := AdicCompletion I C
           toB := Θ
           surjective := hΘs
           sq_zero := hΘsq
           moduleKernel := modInst
           toB_smul_kernel := fun b' x => hsmul b' x
           kernelEquiv := E
           map_I := fun i => by
             have hi : (i : k) = 0 := i.2
             have h5 : (i : ↥(⊥ : Ideal k)) = 0 := Subtype.ext hi
             rw [h5]
             simp only [map_zero, Submodule.coe_zero] },
         IsScalarTower.toAlgHom k C (AdicCompletion I C), fun z => rfl, hgoal⟩

end WithBase

end Abstract

section Concrete

/-- **Stacks 0DZ4**, surjectivity half.  A square-zero extension `0 → N → C → B → 0` of a
`k`-algebra `B` by a finite `B`-module `N`, with `B` Noetherian, induces by `J`-adic
completion a square-zero extension of `B^` by `N^`, together with a compatible `k`-algebra
map `C → C^`. -/
private theorem exists_completed_extension
    {k : Type uk} {B : Type uB} [CommRing k] [CommRing B] [Algebra k B] [IsNoetherianRing B]
    (J : Ideal B) {N : Type uN} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (X : (Stacks.Deformation.algebraExtensionProblem k B N).CompatibleExtension.{max uB uN}) :
    ∃ Y : (Stacks.Deformation.algebraExtensionProblem k (AdicCompletion J B)
        (AdicCompletion J N)).CompatibleExtension.{max uB uN},
      ∃ h : X.B' →ₐ[k] Y.B',
        (∀ z : X.B', Y.toB (h z) = algebraMap B (AdicCompletion J B) (X.toB z)) ∧
          ∀ n : N, h (Stacks.Deformation.kernelInclusion X n) =
            Stacks.Deformation.kernelInclusion Y (AdicCompletion.of J N n) := by
  let : Algebra X.B' B := (X.toB.toRingHom : X.B' →+* B).toAlgebra
  let : IsScalarTower k X.B' B :=
    IsScalarTower.of_algebraMap_eq fun r => (X.toB.commutes r).symm
  let : Module X.B' N := Module.compHom N (algebraMap X.B' B : X.B' →+* B)
  let : IsScalarTower X.B' B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsNoetherianRing X.B' :=
    @isNoetherianRing_compatibleExtension (algebraExtensionProblem k B N)
      (inferInstanceAs (IsNoetherianRing B)) (inferInstanceAs (Module.Finite B N)) X
  have hs : Function.Surjective (algebraMap X.B' B : X.B' → B) := X.surjective
  have hIJ : J = (J.comap (algebraMap X.B' B : X.B' →+* B)).map (algebraMap X.B' B) :=
    (Ideal.map_comap_of_surjective _ hs J).symm
  have hK2 : RingHom.ker (algebraMap X.B' B : X.B' →+* B) ^ 2 = ⊥ := X.sq_zero
  let eKN : N ≃ₗ[X.B'] RingHom.ker (algebraMap X.B' B : X.B' →+* B) :=
    { toFun := X.kernelEquiv
      map_add' := X.kernelEquiv.map_add
      map_smul' := fun c n =>
        (X.kernelEquiv.map_smul (X.toB c) n).trans (X.toB_smul_kernel c _)
      invFun := X.kernelEquiv.symm
      left_inv := X.kernelEquiv.left_inv
      right_inv := X.kernelEquiv.right_inv }
  obtain ⟨Y, h, h1, h2⟩ := exists_extension_abstract (k := k)
    (J.comap (algebraMap X.B' B : X.B' →+* B)) J hIJ hs hK2 eKN
  exact ⟨Y, h, h1, h2⟩

end Concrete


/-! ### Bijectivity of the comparison map along `B → B^` -/

/-- **Stacks 0DZ4**, surjectivity of the comparison map along `B → B^`.  The source's
construction is the completion: a class in `Ext¹_B(NL_{B/k}, N^)` comes from a class with
coefficients in `N` by `Deformation.Examples.bijective_naiveCotangentExtOneMap_adicCompletion`,
hence from a square-zero extension `0 → N → C → B → 0`, and the `J_C`-adic completion of `C` is
an extension of `B^` by `N^` restricting to it, by **Stacks 0GPV** applied to `C → C^`. -/
public theorem surjective_naiveCotangentExtOneTowerMap_adicCompletion
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    Function.Surjective (naiveCotangentExtOneTowerMap k B (AdicCompletion J B)
      (N := AdicCompletion J N)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  intro ξ
  obtain ⟨ξ₀, hξ₀⟩ := (bijective_naiveCotangentExtOneMap_adicCompletion k B J hsm N).2 ξ
  let eB := squareZeroAlgebraExtensionClassesEquivExtOne k B N
  obtain ⟨X, hX⟩ := Quotient.exists_rep (eB.symm ξ₀)
  have hXξ : eB ⟦X⟧ = ξ₀ := by rw [hX]; exact eB.apply_symm_apply ξ₀
  obtain ⟨Y, h, hhB, hhN⟩ := exists_completed_extension J X
  refine ⟨squareZeroAlgebraExtensionClassesEquivExtOne k (AdicCompletion J B)
    (AdicCompletion J N) ⟦Y⟧, ?_⟩
  have hgpv := (exists_compatible_algebraMap_iff k B (AdicCompletion J B)
    (AdicCompletion.of J N) X Y).mp ⟨h, hhB, hhN⟩
  rw [← hgpv, hXξ, hξ₀]

/-- **Stacks 0DZ4**, bijectivity of the comparison map along `B → B^`: every square-zero
extension of `B` by `N^` comes from exactly one square-zero extension of `B^` by `N^`. -/
public theorem bijective_naiveCotangentExtOneTowerMap_adicCompletion
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    Function.Bijective (naiveCotangentExtOneTowerMap k B (AdicCompletion J B)
      (N := AdicCompletion J N)) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  exact ⟨injective_naiveCotangentExtOneTowerMap_adicCompletion k B J N,
    surjective_naiveCotangentExtOneTowerMap_adicCompletion k B J hsm N⟩

/-! ### The completion bijection -/

/-- The split square-zero extension of `B` by `N` and the split square-zero extension of the
`J`-adic completions admit a `k`-algebra map of middle rings over `B → B^` and over `N → N^`. -/
public theorem exists_compatible_algebraMap_splitAlgebraExtension_adicCompletion
    (k : Type uk) (B : Type uB) [CommRing k] [CommRing B] [Algebra k B]
    (J : Ideal B) (N : Type uN) [AddCommGroup N] [Module B N] :
    ∃ h : (splitAlgebraExtension k B N).B' →ₐ[k]
        (splitAlgebraExtension k (AdicCompletion J B) (AdicCompletion J N)).B',
      (∀ z : (splitAlgebraExtension k B N).B',
          (splitAlgebraExtension k (AdicCompletion J B) (AdicCompletion J N)).toB (h z) =
            algebraMap B (AdicCompletion J B) ((splitAlgebraExtension k B N).toB z)) ∧
        ∀ n : N, h (kernelInclusion (splitAlgebraExtension k B N) n) =
          kernelInclusion (splitAlgebraExtension k (AdicCompletion J B) (AdicCompletion J N))
            (AdicCompletion.of J N n) := by
  rw [exists_compatible_algebraMap_iff k B (AdicCompletion J B) (AdicCompletion.of J N),
    squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero,
    squareZeroAlgebraExtensionClassesEquivExtOne_split_eq_zero, map_zero, map_zero]

/-- **Stacks 0DZ4.** For a finite type algebra `B` over a field `k` which is smooth over `k`
outside the zero set of an ideal `J`, and a finite `B`-module `N`, completion along `J` is a
bijection from the isomorphism classes of square-zero extensions of `B` by `N` to those of `B^`
by `N^`, matching a class with its image exactly when the two extensions admit a `k`-algebra map
of middle rings over `B → B^` and over `N → N^`. -/
@[stacks 0DZ4]
public theorem exists_squareZeroAlgebraExtensionClassesCompletionEquiv
    (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (J : Ideal B)
    (hsm : ∀ q : PrimeSpectrum B, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (N : Type uN) [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ e : SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
        max uB uN} (algebraExtensionProblem k B N) ≃
      SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{uk, uk, uB, uN,
        max uB uN} (algebraExtensionProblem k (AdicCompletion J B) (AdicCompletion J N)),
      ∀ (X : (algebraExtensionProblem k B N).CompatibleExtension.{max uB uN})
        (Y : (algebraExtensionProblem k (AdicCompletion J B)
          (AdicCompletion J N)).CompatibleExtension.{max uB uN}),
        (∃ h : X.B' →ₐ[k] Y.B',
            (∀ z : X.B', Y.toB (h z) = algebraMap B (AdicCompletion J B) (X.toB z)) ∧
              ∀ n : N, h (kernelInclusion X n) =
                kernelInclusion Y (AdicCompletion.of J N n)) ↔
          e ⟦X⟧ = ⟦Y⟧ := by
  have hmod := bijective_naiveCotangentExtOneMap_adicCompletion k B J hsm N
  have htower := bijective_naiveCotangentExtOneTowerMap_adicCompletion k B J hsm N
  obtain ⟨f, hf⟩ : ∃ f : _ ≃ _, ∀ Z, f Z = naiveCotangentExtOneMap k B (AdicCompletion.of J N)
      (squareZeroAlgebraExtensionClassesEquivExtOne k B N Z) :=
    ⟨(squareZeroAlgebraExtensionClassesEquivExtOne k B N).trans (Equiv.ofBijective _ hmod),
      fun _ ↦ rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : _ ≃ _, ∀ Z, g Z =
      naiveCotangentExtOneTowerMap k B (AdicCompletion J B)
        (squareZeroAlgebraExtensionClassesEquivExtOne k (AdicCompletion J B)
          (AdicCompletion J N) Z) :=
    ⟨(squareZeroAlgebraExtensionClassesEquivExtOne k (AdicCompletion J B)
      (AdicCompletion J N)).trans (Equiv.ofBijective _ htower), fun _ ↦ rfl⟩
  refine ⟨f.trans g.symm, fun X Y ↦ ?_⟩
  have htr : (f.trans g.symm) ⟦X⟧ = g.symm (f ⟦X⟧) := rfl
  have hsym : g.symm (f ⟦X⟧) = ⟦Y⟧ ↔ f ⟦X⟧ = g ⟦Y⟧ := Equiv.symm_apply_eq g
  rw [htr, hsym, hf ⟦X⟧, hg ⟦Y⟧]
  exact exists_compatible_algebraMap_iff k B (AdicCompletion J B)
    (AdicCompletion.of J N) X Y

end Deformation.Examples

end
