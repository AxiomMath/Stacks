module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.SectionCochain
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.SquareModel
public import StacksFrontier.Algebra.Module.FibreSpanningGenerator

/-!
# Sections of a normalized invertible module

Let `X` be a proper scheme over a field `k` covered by two affine opens, let `A` be a
`k`-algebra and let `L` be an invertible module on `X_A` all of whose fibres have
`H¹ = 0` and `dim H⁰ = 1`. A global section `s` of `L` that pulls back to a nonzero section on
every fibre generates `Γ(X_A, L)` freely: every global section is `a • s` for a unique `a ∈ A`.
This is the algebra behind the uniqueness of the divisor attached to a point of the subfunctor
`F` of [Stacks, Tag 0B9V] in the proof of [Stacks, Tag 0B9X].

## Main results

* `Stacks.TwoAffineCech.existsUnique_smul_eq_of_fibres`: the free generation statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.FibreCohomology
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A] {XT : Scheme.{u}} (gT : XT ⟶ X)
  (fT : XT ⟶ Spec (.of A))
  (hT : IsPullback gT fT fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  (L : XT.Modules) [Stacks.Ample.IsInvertibleModule XT L]
  (h1 : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
    (fibreCohomology fT L x 1) = 0)
  (h0 : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
    (fibreCohomology fT L x 0) = 1)

/-- **A section is nonzero at some field point over `p`**: for a ring map `φ : A → K` to a field
with kernel `p` and a cartesian square over it, the pullback of the section to the base change
of `XT` to `K` is nonzero. -/
def NonzeroAtFieldPoint (s : Γ(L, ⊤)) (p : PrimeSpectrum A) : Prop :=
  ∃ (K : Type u) (_ : Field K) (φ : A →+* K) (_ : RingHom.ker φ = p.asIdeal) (X' : Scheme.{u})
    (f' : X' ⟶ Spec (.of K)) (g' : X' ⟶ XT),
    IsPullback g' f' fT (Spec.map (CommRingCat.ofHom φ)) ∧ pullbackGlobalSections g' L s ≠ 0

include hU hUaff hT h1 h0 in
/-- The fibres of `H⁰(X_A, L)` are one-dimensional. -/
theorem finrank_residueField_tensor_ker_eq_one (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (cechD fT (sqCover U gT) L)) = 1 := by
  rw [finrank_residueField_tensor_ker_cechD_of_isPullback fX U hU hUaff gT fT hT L h1 p]
  exact h0 _

include hU hUaff hT in
/-- A section nonzero at some field point over `p` has a cocycle surviving in the fibre at `p`. -/
theorem tmul_sectionCocycle_ne_zero (s : Γ(L, ⊤)) (p : PrimeSpectrum A)
    (hs : NonzeroAtFieldPoint fT L s p) :
    (1 : p.asIdeal.ResidueField) ⊗ₜ[A] sectionCocycle fT (sqCover U gT) L s ≠ 0 := by
  have hL : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have : IsSeparated fT := isSeparated_of_isPullback' fX gT fT hT
  obtain ⟨K, _, φ, hker, X', f', g', hsq, hne⟩ := hs
  have h := tmul_ne_zero_of_pullbackGlobalSections_ne_zero φ fT f' g' hsq
    (sqCover U gT) L (isAffineOpen_sqCover fX U hUaff gT fT hT) (iSup_sqCover U hU gT) s hne
  exact fun h0 => h (Module.tmul_eq_zero_of_ker φ _ p hker h0)

include hU hUaff hT h1 h0 in
/-- **A section that is nonzero on every fibre generates `H⁰(X_A, L)`.** -/
theorem span_sectionCocycle_eq_top (s : Γ(L, ⊤))
    (hs : ∀ p : PrimeSpectrum A, NonzeroAtFieldPoint fT L s p) :
    Submodule.span A {sectionCocycle fT (sqCover U gT) L s} = ⊤ := by
  have hfin := (projective_ker_cechD_of_isPullback fX U hU hUaff gT fT hT L h1).1
  refine Module.span_singleton_eq_top_of_fibres _ fun p => ?_
  exact Module.span_singleton_eq_top_of_finrank_eq_one
    (finrank_residueField_tensor_ker_eq_one fX U hU hUaff gT fT hT L h1 h0 p)
    (tmul_sectionCocycle_ne_zero fX U hU hUaff gT fT hT L s p (hs p))

include hU hUaff hT h1 h0 in
/-- **A section that is nonzero on every fibre generates `Γ(X_A, L)` freely**: every global
section is `a • s` for a unique `a ∈ A`, `A` acting through `X_A ⟶ Spec A`. -/
theorem existsUnique_smul_eq_of_fibres (s : Γ(L, ⊤))
    (hs : ∀ p : PrimeSpectrum A, NonzeroAtFieldPoint fT L s p)
    (t : Γ(L, ⊤)) :
    ∃! a : A, t = (Stacks.Cech.baseRingHom fT ⊤).hom a • s := by
  have hL : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have : IsSeparated fT := isSeparated_of_isPullback' fX gT fT hT
  obtain ⟨hfin, hproj⟩ := projective_ker_cechD_of_isPullback fX U hU hUaff gT fT hT L h1
  have hspan := span_sectionCocycle_eq_top fX U hU hUaff gT fT hT L h1 h0 s hs
  have hcoc : ∀ a : A, sectionCocycle fT (sqCover U gT) L
      ((Stacks.Cech.baseRingHom fT ⊤).hom a • s) =
        a • sectionCocycle fT (sqCover U gT) L s := fun a =>
    Subtype.ext (Subtype.ext (sectionCochain_smul fT (sqCover U gT) L a s))
  have hinj : Function.Injective (sectionCocycle fT (sqCover U gT) L) :=
    fun x y hxy => sectionCochain_injective (sqCover U gT) L (iSup_sqCover U hU gT)
      (congrArg (fun z : LinearMap.ker (cechD fT (sqCover U gT) L) =>
        altCochain fT (sqCover U gT) L z.1) hxy)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (hspan.symm ▸ Submodule.mem_top :
      sectionCocycle fT (sqCover U gT) L t ∈
        Submodule.span A {sectionCocycle fT (sqCover U gT) L s})
  refine ⟨a, hinj (ha.symm.trans (hcoc a).symm), fun b hb => ?_⟩
  have hfree := Module.injective_smul_of_fibres _ hspan
    (finrank_residueField_tensor_ker_eq_one fX U hU hUaff gT fT hT L h1 h0)
  refine hfree ?_
  show b • _ = a • _
  exact (hcoc b).symm.trans ((congrArg _ hb.symm).trans ha.symm)

include hU hUaff hT h1 h0 in
/-- **Locally on `Spec A` there is a section whose cocycle survives in every fibre.** -/
theorem exists_section_tmul_ne_zero (y : PrimeSpectrum A) :
    ∃ (s : Γ(L, ⊤)) (O : Set (PrimeSpectrum A)), IsOpen O ∧ y ∈ O ∧
      ∀ p ∈ O, (1 : p.asIdeal.ResidueField) ⊗ₜ[A] sectionCocycle fT (sqCover U gT) L s ≠ 0 := by
  have hL : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have : IsSeparated fT := isSeparated_of_isPullback' fX gT fT hT
  obtain ⟨hfin, -⟩ := projective_ker_cechD_of_isPullback fX U hU hUaff gT fT hT L h1
  set M := LinearMap.ker (cechD fT (sqCover U gT) L)
  have hdim := finrank_residueField_tensor_ker_eq_one fX U hU hUaff gT fT hT L h1 h0
  obtain ⟨m, hm⟩ : ∃ m : M, (1 : y.asIdeal.ResidueField) ⊗ₜ[A] m ≠ 0 := by
    by_contra! hall
    have hz : ∀ z : y.asIdeal.ResidueField ⊗[A] M, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul c n =>
        rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', hall n, smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    have : Subsingleton (y.asIdeal.ResidueField ⊗[A] M) :=
      ⟨fun a b => (hz a).trans (hz b).symm⟩
    have h1' := hdim y
    rw [Module.finrank_zero_of_subsingleton] at h1'
    exact zero_ne_one h1'
  obtain ⟨s, rfl⟩ := exists_sectionCocycle_eq fT (sqCover U gT) L (iSup_sqCover U hU gT) m
  refine ⟨s, _, Module.isOpen_setOf_span_tmul_eq_top _,
    Module.span_singleton_eq_top_of_finrank_eq_one (hdim y) hm, fun p hp h => ?_⟩
  have hp' : Submodule.span p.asIdeal.ResidueField
      {(1 : p.asIdeal.ResidueField) ⊗ₜ[A] sectionCocycle fT (sqCover U gT) L s} = ⊤ := hp
  rw [h, Submodule.span_singleton_eq_bot.2 rfl] at hp'
  have := hdim p
  rw [← finrank_top, ← hp', finrank_bot] at this
  exact zero_ne_one this

include hU hUaff hT h1 h0 in
/-- **Locally on `Spec A` there is a section that is nonzero on the fibre at every field point.**
For each point `y` there are a global section `s` of `L` and an open `O ∋ y` such that `s` pulls
back to a nonzero section on every base change of `XT` to a field `K` along a ring map
`A → K` whose kernel is a point of `O`. -/
theorem exists_section_ne_zero_on_fieldPoints (y : PrimeSpectrum A) :
    ∃ (s : Γ(L, ⊤)) (O : Set (PrimeSpectrum A)), IsOpen O ∧ y ∈ O ∧
      ∀ (K : Type u) [Field K] (φ : A →+* K) (p : PrimeSpectrum A), p ∈ O →
        RingHom.ker φ = p.asIdeal → ∀ {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of K)) (g' : X' ⟶ XT),
          IsPullback g' f' fT (Spec.map (CommRingCat.ofHom φ)) →
            pullbackGlobalSections g' L s ≠ 0 := by
  have hL : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  have : IsSeparated fT := isSeparated_of_isPullback' fX gT fT hT
  obtain ⟨s, O, hO, hyO, hs⟩ := exists_section_tmul_ne_zero fX U hU hUaff gT fT hT L h1 h0 y
  refine ⟨s, O, hO, hyO, fun K _ φ p hp hker X' f' g' hsq => ?_⟩
  have := flat_cech_of_isPullback fX U hUaff gT fT hT L 1
  exact pullbackGlobalSections_ne_zero_of_tmul_ne_zero φ fT f' g' hsq (sqCover U gT) L
    (isAffineOpen_sqCover fX U hUaff gT fT hT)
    (surjective_cechD_of_isPullback fX U hU hUaff gT fT hT L h1) s
    (Module.tmul_ne_zero_of_ker φ _ p hker (hs p hp))

end Stacks.TwoAffineCech
