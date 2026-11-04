module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Spanning families of finite locally free modules

Let `M` be a finite locally free module of rank `d` over a commutative ring `A` and let
`v₁, …, v_d ∈ M`.

* If the `v_l` generate `M`, they form a basis of `M`: the map `A^d → M` they define is
  surjective, hence an isomorphism. This is the parenthetical "surjective (equivalently an
  isomorphism)" in the source's proof of [Stacks, Tag 0B99].
* If, for some `A`-algebra `B` and some prime `q ⊂ B` lying over `p ⊂ A`, the elements `1 ⊗ v_l`
  generate `B ⊗_A M`, then the `v_l` generate `M_g` for some `g ∉ p`. Only finiteness of `M` is
  used. This is the openness step of the source's proof ("by Nakayama's lemma there is an open
  neighbourhood").

## Main results

* `Module.IsFiniteLocallyFreeOfRank.linearIndependent_of_span_eq_top`
* `Module.exists_away_surjective_linearCombination_of_baseChange`

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public section

open TensorProduct

universe u v w

/-- **A spanning family of `d` elements of a finite locally free module of rank `d` is linearly
independent.** -/
theorem Module.IsFiniteLocallyFreeOfRank.linearIndependent_of_span_eq_top {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] {d : ℕ}
    (hM : Module.IsFiniteLocallyFreeOfRank A M d) (v : Fin d → M)
    (hv : Submodule.span A (Set.range v) = ⊤) : LinearIndependent A v := by
  obtain ⟨ι, f, hspan, hb⟩ := hM
  let φ : (Fin d → A) →ₗ[A] M := Fintype.linearCombination A v
  have hφs : Function.Surjective φ := by
    rwa [← LinearMap.range_eq_top, Fintype.range_linearCombination]
  have hinj : Function.Injective φ := by
    refine injective_of_isLocalized_span (Set.range f) hspan
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) (Fin d → A))
      (fun r ↦ LocalizedModule.mkLinearMap (Submonoid.powers r.1) (Fin d → A))
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) M)
      (fun r ↦ LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) φ ?_
    rintro ⟨r, i, rfl⟩
    let S := Submonoid.powers (f i)
    let b := (hb i).some
    let b₁ : Module.Basis (Fin d) (Localization S) (LocalizedModule S (Fin d → A)) :=
      (Pi.basisFun A (Fin d)).ofIsLocalizedModule (Localization S) S
        (LocalizedModule.mkLinearMap S (Fin d → A))
    have : Module.Finite (Localization S) (LocalizedModule S M) := Module.Finite.of_basis b
    let e := b₁.equiv b (Equiv.refl _)
    exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap
      (LocalizedModule.map S φ) e.injective (LocalizedModule.map_surjective S φ hφs)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have : φ c = φ 0 := by rwa [map_zero, Fintype.linearCombination_apply]
  exact congrFun (hinj this)

/-- If the `1 ⊗ v_l` generate `B ⊗_A M`, then `B ⊗_A (M / ⟨v⟩) = 0`. -/
theorem Module.subsingleton_baseChange_quotient_span {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] {d : ℕ} (v : Fin d → M)
    {B : Type w} [CommRing B] [Algebra A B]
    (hv : Submodule.span B (Set.range fun l ↦ (1 : B) ⊗ₜ[A] v l) = ⊤) :
    Subsingleton (B ⊗[A] (M ⧸ LinearMap.range (Fintype.linearCombination A v))) := by
  let N := LinearMap.range (Fintype.linearCombination A v)
  let π : B ⊗[A] M →ₗ[B] B ⊗[A] (M ⧸ N) := LinearMap.baseChange B N.mkQ
  have hπ : Function.Surjective π :=
    LinearMap.baseChange_surjective _ (Submodule.mkQ_surjective N)
  have h0 : ∀ l, π ((1 : B) ⊗ₜ[A] v l) = 0 := by
    intro l
    have hl : v l ∈ N := ⟨Pi.single l 1, by
      classical
      rw [Fintype.linearCombination_apply_single, one_smul]⟩
    simp [π, (Submodule.Quotient.mk_eq_zero N).mpr hl]
  have htop : π = 0 := by
    rw [← LinearMap.range_eq_bot, LinearMap.range_eq_map, ← hv, Submodule.map_span, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    simp [h0 l]
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hπ x
  obtain ⟨y, rfl⟩ := hπ y
  rw [htop, LinearMap.zero_apply, LinearMap.zero_apply]

/-- **Spanning descends to a neighbourhood of a point.** Let `M` be a finite `A`-module, `B` an
`A`-algebra and `q ⊂ B` a prime lying over `p ⊂ A`. If the `1 ⊗ v_l` generate `B ⊗_A M`, there
is `g ∉ p` such that the `v_l` generate `M_g`. -/
theorem Module.exists_away_surjective_linearCombination_of_baseChange {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] {d : ℕ} (v : Fin d → M)
    {B : Type u} [CommRing B] [Algebra A B] (q : Ideal B) [q.IsPrime]
    (hv : Submodule.span B (Set.range fun l ↦ (1 : B) ⊗ₜ[A] v l) = ⊤) :
    ∃ g ∉ q.comap (algebraMap A B),
      Function.Surjective
        (LocalizedModule.map (Submonoid.powers g) (Fintype.linearCombination A v)) := by
  let φ := Fintype.linearCombination A v
  let p := q.comap (algebraMap A B)
  let C := M ⧸ LinearMap.range φ
  have hBC : Subsingleton (B ⊗[A] C) := Module.subsingleton_baseChange_quotient_span v hv
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A C := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro hnt
    let : Algebra p.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map p q (algebraMap A B) rfl).toAlgebra
    have : IsScalarTower A p.ResidueField q.ResidueField := IsScalarTower.of_algebraMap_eq
      fun a ↦ by
        change algebraMap A q.ResidueField a =
          Ideal.ResidueField.map p q (algebraMap A B) rfl (algebraMap A p.ResidueField a)
        rw [Ideal.ResidueField.map_algebraMap, IsScalarTower.algebraMap_apply A B]
    have h1 : Nontrivial (q.ResidueField ⊗[p.ResidueField] (p.ResidueField ⊗[A] C)) :=
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _).mpr hnt
    have e1 := AlgebraTensorModule.cancelBaseChange A p.ResidueField q.ResidueField
      q.ResidueField C
    have e2 := AlgebraTensorModule.cancelBaseChange A B q.ResidueField q.ResidueField C
    have h2 : Nontrivial (q.ResidueField ⊗[B] (B ⊗[A] C)) :=
      e2.toEquiv.nontrivial_congr.mpr (e1.toEquiv.nontrivial_congr.mp h1)
    exact not_subsingleton (q.ResidueField ⊗[B] (B ⊗[A] C)) inferInstance
  have hloc : Subsingleton (LocalizedModule p.primeCompl C) :=
    (Module.notMem_support_iff).mp hnot
  obtain ⟨g, hg, hsub⟩ := LocalizedModule.exists_subsingleton_away (M := C) p
  exact ⟨g, hg, by rwa [φ.localizedMap_surjective_iff_subsingleton_localized_coker]⟩
