module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp

/-!
# The rank of a composition of finite locally free morphisms

If `f : X ⟶ Y` is finite locally free of rank `r` and `g : Y ⟶ Z` is finite locally free of rank
`s`, then `f ≫ g` is finite locally free of rank `r * s`.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq_mul`: for a field `k`, a finite
  `k`-algebra `B` and a `B`-module `A` that is finite locally free of rank `r`, the `k`-dimension
  of `A` is `r` times the `k`-dimension of `B`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_comp_of_specTarget`: the rank of a composition of
  finite locally free morphisms over the spectrum of a field is the product of the ranks.
* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp`: the rank of a composition of finite locally
  free morphisms is the product of the ranks.

## References

* [Stacks Project, Tag 02KC](https://stacks.math.columbia.edu/tag/02KC)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Module

/-- Let `k` be a field, let `B` be a finite `k`-algebra and let `A` be a `B`-module that is finite
locally free of rank `r`. Then `A` is a finite `k`-module of dimension `r * dim_k B`. -/
theorem IsFiniteLocallyFreeOfRank.finite_and_finrank_eq_mul {k B A : Type u} [Field k]
    [CommRing B] [Algebra k B] [AddCommGroup A] [Module B A] [Module k A] [IsScalarTower k B A]
    [Module.Finite k B] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank B A r) :
    Module.Finite k A ∧ Module.finrank k A = r * Module.finrank k B := by
  have hfin : Module.Finite B A := h.finite
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : Subsingleton A := Module.subsingleton B A
    refine ⟨inferInstance, ?_⟩
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, mul_zero]
  have hfl : Module.IsFiniteLocallyFree B A := by
    obtain ⟨ι, f, hspan, hb⟩ := h
    exact ⟨ι, f, hspan, fun i ↦ ⟨Module.Free.of_basis (hb i).some,
      Module.Finite.of_basis (hb i).some⟩⟩
  have hproj : Module.Projective B A :=
    ((Module.isFiniteLocallyFree_iff_finite_projective B A).mp hfl).2
  have hflat : Module.Flat B A := Module.Flat.of_projective
  have hart : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B A r fun P ↦ by
    have : P.asIdeal.IsMaximal := P.2
    let : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field _
    exact Module.IsFiniteLocallyFreeOfRank.finrank_eq (K := B ⧸ P.asIdeal) (h.baseChange _)
  have : Module.Free B A := Module.Free.of_basis b
  refine ⟨Module.Finite.trans B A, ?_⟩
  rw [← Module.finrank_mul_finrank k B A, Module.finrank_eq_card_basis b, Fintype.card_fin,
    mul_comm]

end Module

namespace Stacks.Morphisms

/-- If `p : W ⟶ T` is finite locally free of rank `r` and `p₀ : T ⟶ Spec K` is finite locally
free of rank `s` over a field `K`, then `p ≫ p₀` is finite locally free of rank `r * s`. -/
theorem isFiniteLocallyFreeOfRank_comp_of_specTarget {K : Type u} [Field K] {W T : Scheme.{u}}
    (p : W ⟶ T) (p₀ : T ⟶ Spec (.of K)) (r s : ℕ) [hp : IsFiniteLocallyFreeOfRank p r]
    [h₀ : IsFiniteLocallyFreeOfRank p₀ s] :
    IsFiniteLocallyFreeOfRank (p ≫ p₀) (r * s) := by
  have : IsAffineHom p₀ := h₀.toIsAffineHom
  have : IsAffineHom p := hp.toIsAffineHom
  have : IsAffine T := isAffine_of_isAffineHom p₀
  let : Algebra K ↑Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p₀.appTop).hom.toAlgebra
  let : Algebra ↑Γ(T, ⊤) ↑Γ(W, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra K ↑Γ(W, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ (p ≫ p₀).appTop).hom.toAlgebra
  have : IsScalarTower K ↑Γ(T, ⊤) ↑Γ(W, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    show (p ≫ p₀).appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom x) =
      p.appTop.hom (p₀.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom x))
    rw [show (p ≫ p₀).appTop = p₀.appTop ≫ p.appTop from Scheme.Hom.comp_appTop p p₀]
    rfl
  obtain ⟨hTfin, hTrank⟩ :=
    (isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget p₀ s rfl).mp h₀
  have hmod : Module.IsFiniteLocallyFreeOfRank ↑Γ(T, ⊤) ↑Γ(W, ⊤) r :=
    (isFiniteLocallyFreeOfRank_iff_module_of_isAffine p r rfl).mp hp
  obtain ⟨hWfin, hWrank⟩ :=
    Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq_mul (k := K) hmod
  refine (isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget (p ≫ p₀) (r * s) rfl).mpr
    ⟨hWfin, ?_⟩
  rw [hWrank, hTrank]

/-- If `f : X ⟶ Y` is finite locally free of rank `r` and `g : Y ⟶ Z` is finite locally free of
rank `s`, then `f ≫ g` is finite locally free of rank `r * s`. -/
theorem IsFiniteLocallyFreeOfRank.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ)
    [hf : IsFiniteLocallyFreeOfRank f r] [hg : IsFiniteLocallyFreeOfRank g s] :
    IsFiniteLocallyFreeOfRank (f ≫ g) (r * s) := by
  have hflf : IsFiniteLocallyFree (f ≫ g) := by
    have := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r
    have := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree g s
    infer_instance
  obtain ⟨_, _, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation (f ≫ g)).mp hflf
  rw [isFiniteLocallyFreeOfRank_iff_forall_finrank_eq (f ≫ g) (r * s)]
  intro z
  obtain ⟨t₀, -⟩ : z ∈ Set.range (Z.fromSpecResidueField z).base := by
    rw [Scheme.range_fromSpecResidueField]
    exact rfl
  have t : IsPullback (pullback.fst g (Z.fromSpecResidueField z))
      (pullback.snd g (Z.fromSpecResidueField z)) g (Z.fromSpecResidueField z) :=
    IsPullback.of_hasPullback g (Z.fromSpecResidueField z)
  have sq : IsPullback (pullback.fst f (pullback.fst g (Z.fromSpecResidueField z)))
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z))) f
      (pullback.fst g (Z.fromSpecResidueField z)) :=
    IsPullback.of_hasPullback f (pullback.fst g (Z.fromSpecResidueField z))
  have hg' : IsFiniteLocallyFreeOfRank (pullback.snd g (Z.fromSpecResidueField z)) s :=
    IsFiniteLocallyFreeOfRank.of_isPullback t
  have hf' : IsFiniteLocallyFreeOfRank
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z))) r :=
    IsFiniteLocallyFreeOfRank.of_isPullback sq
  have hcomp : IsFiniteLocallyFreeOfRank
      (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z)) ≫
        pullback.snd g (Z.fromSpecResidueField z)) (r * s) :=
    isFiniteLocallyFreeOfRank_comp_of_specTarget (K := (Z.residueField z : Type u)) _ _ r s
  obtain ⟨_, _, -⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (r * s) (h := hcomp))
  have key := Scheme.Hom.finrank_of_isPullback
    (pullback.fst f (pullback.fst g (Z.fromSpecResidueField z)))
    (pullback.snd f (pullback.fst g (Z.fromSpecResidueField z)) ≫
      pullback.snd g (Z.fromSpecResidueField z)) (f ≫ g) (Z.fromSpecResidueField z)
    (sq.paste_vert t) t₀
  rw [Z.fromSpecResidueField_apply z t₀] at key
  rw [← key, (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ (r * s)).mp hcomp t₀]

end Stacks.Morphisms

end
