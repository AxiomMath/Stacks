module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow

/-!
# Unramified homomorphisms of local rings and their completions

An unramified local homomorphism of Noetherian local rings induces a finite map on completions
at the maximal ideals. That map is surjective as soon as the induced map of residue fields is
bijective, in particular whenever the residue field of the source is separably closed. For
complete discrete valuation rings, unramifiedness is detected by a uniformizer together with
the residue field extension.

## Main results

* `RingHom.moduleFinite_adicCompletion_of_formallyUnramified`: the completion of the target is
  a finite module over the completion of the source.
* `RingHom.surjective_adicCompletionMap_of_bijective_residueFieldMap`: the map on completions
  is surjective when the residue field map is bijective.
* `RingHom.surjective_adicCompletionMap_of_isSepClosed`: the same conclusion when the residue
  field of the source is separably closed.
* `RingHom.unramified_iff_uniformizer_and_residueField`: the characterization of unramified
  homomorphisms of complete discrete valuation rings.

## Implementation notes

The completion of a local ring `R` is `AdicCompletion (IsLocalRing.maximalIdeal R) R` and the
induced map on completions is `adicCompletionMap`. Unramifiedness of a homomorphism of local
rings is recorded as `RingHom.FormallyUnramified` together with `RingHom.EssFiniteType`.

Finiteness is obtained by comparing two completions of the target: along the maximal ideal of
the source and along the ideal it generates. These agree because the two filtrations coincide
termwise, and `adicCompletionLinearEquivMap` records the resulting identification.
Surjectivity is then Nakayama's lemma applied to the finite module structure.

Equality of residue fields in the second statement means that the canonical residue field map
is bijective, and a uniformizer of a discrete valuation ring is an irreducible element.

## References

* [Stacks Project, Tag 039H](https://stacks.math.columbia.edu/tag/039H)
-/

@[expose] public section

universe u v

open AdicCompletion IsLocalRing

namespace RingHom

/-- **Stacks Project, Tag 039H**, part (1). The completion of the target of an unramified local
homomorphism of Noetherian local rings is a finite module over the completion of the source. -/
@[stacks 039H "part (1)", ega "IV 17.4.4" "f) finiteness of B̂/Â"]
theorem moduleFinite_adicCompletion_of_formallyUnramified
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hfu : f.FormallyUnramified) (hft : f.EssFiniteType) :
    letI := (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)).toAlgebra
    Module.Finite (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.FormallyUnramified A B := hfu
  have : Algebra.EssFiniteType A B := hft
  have hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hresfin : Module.Finite A (ResidueField B) := by
    have : Algebra.FormallyUnramified A (ResidueField B) :=
      Algebra.FormallyUnramified.comp A B (ResidueField B)
    have : Algebra.FormallyUnramified (ResidueField A) (ResidueField B) :=
      Algebra.FormallyUnramified.of_restrictScalars A _ _
    have : Algebra.EssFiniteType A (ResidueField B) := Algebra.EssFiniteType.comp A B _
    have : Algebra.EssFiniteType (ResidueField A) (ResidueField B) :=
      Algebra.EssFiniteType.of_comp A _ _
    have : Module.Finite (ResidueField A) (ResidueField B) :=
      Algebra.FormallyUnramified.finite_of_free _ _
    exact Module.Finite.trans (ResidueField A) (ResidueField B)
  have : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
    rwa [hmax]
  have hcomp := AdicCompletion.nonempty_algEquiv_map_and_finite
    (R := A) (S := B) ((maximalIdeal A).fg_of_isNoetherianRing)
  set I := maximalIdeal A
  set Rhat := AdicCompletion I A
  set C := AdicCompletion (I.map (algebraMap A B)) B
  let : Algebra Rhat C := (AdicCompletion.completionMap (B := B) I).toRingHom.toAlgebra
  let E : AdicCompletion I B ≃ₗ[Rhat] C :=
    { __ := adicCompletionLinearEquivMap I B
      map_smul' := by
        intro x y
        refine Subtype.ext (funext fun n ↦ ?_)
        obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
          (I ^ n • (⊤ : Submodule A A)) (x.val n)
        obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective
          (I ^ n • (⊤ : Submodule A B)) (y.val n)
        have hL : (x • y).val n = Submodule.Quotient.mk (algebraMap A B a * b) := by
          rw [AdicCompletion.smul_eval, ← ha, ← hb, ← Algebra.smul_def a b]
          rfl
        change quotEquivMapPow I B n ((x • y).val n) =
          ((AdicCompletion.completionMap (B := B) I x) *
            adicCompletionLinearEquivMap I B y).val n
        rw [hL, quotEquivMapPow_mk, AdicCompletion.val_mul,
          AdicCompletion.val_completionMap I n x a ha.symm]
        change _ = _ * quotEquivMapPow I B n (y.val n)
        rw [← hb, quotEquivMapPow_mk]
        rfl }
  have transport (J : Ideal B) (hJ : (maximalIdeal A).map (algebraMap A B) = J) :
      let := (adicCompletionMap f (maximalIdeal A) J (hJ ▸ le_rfl)).toAlgebra
      Module.Finite Rhat (AdicCompletion J B) := by
    cases hJ
    exact hcomp.2.equiv E
  exact transport (maximalIdeal B) hmax

/-- **Stacks Project, Tag 039H**, part (2). An unramified local homomorphism inducing a
bijection on residue fields induces a surjection on completions. -/
@[stacks 039H "part (2)",
  ega "IV 17.4.4" "f'') when k(x)=k(y)",
  sga "1 I 3.7" "unram ⇒ surj, κ(A)=κ(B)", sga "3 XI 1.3" "(ii) completion surj."]
theorem surjective_adicCompletionMap_of_bijective_residueFieldMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hfu : f.FormallyUnramified) (hft : f.EssFiniteType)
    (hκ : Function.Bijective (ResidueField.map f)) :
    Function.Surjective
      (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)) := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.FormallyUnramified A B := hfu
  have : Algebra.EssFiniteType A B := hft
  set Rhat := AdicCompletion (maximalIdeal A) A
  set Bhat := AdicCompletion (maximalIdeal B) B
  set g := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  let : Algebra Rhat Bhat := g.toAlgebra
  have hcomp : g.comp (algebraMap A Rhat) = (algebraMap B Bhat).comp f :=
    adicCompletionMap_comp_algebraMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)
  have hmaxf : (maximalIdeal A).map f = maximalIdeal B := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B))
  have hmax : (maximalIdeal Rhat).map g = maximalIdeal Bhat := by
    rw [AdicCompletion.maximalIdeal_eq_map (R := A), Ideal.map_map, hcomp, ← Ideal.map_map,
      hmaxf, AdicCompletion.maximalIdeal_eq_map (R := B)]
  have : IsLocalHom g := (IsLocalRing.local_hom_TFAE g).out 3 1 |>.mp hmax.le
  have hiA : Function.Bijective (ResidueField.map (algebraMap A Rhat)) :=
    AdicCompletion.residueField_map_bijective A
  have hiB : Function.Bijective (ResidueField.map (algebraMap B Bhat)) :=
    AdicCompletion.residueField_map_bijective B
  have hrescomp : (ResidueField.map g).comp (ResidueField.map (algebraMap A Rhat)) =
      (ResidueField.map (algebraMap B Bhat)).comp (ResidueField.map f) := by
    ext x
    obtain ⟨a, rfl⟩ := residue_surjective (R := A) x
    simp only [RingHom.comp_apply, ResidueField.map_residue]
    rw [show g (algebraMap A Rhat a) = algebraMap B Bhat (f a) from DFunLike.congr_fun hcomp a]
  have hkg : Function.Bijective (ResidueField.map g) :=
    (hiA.of_comp_iff (ResidueField.map g)).mp (by
      change Function.Bijective ((ResidueField.map g).comp (ResidueField.map (algebraMap A Rhat)))
      rw [hrescomp]
      exact hiB.comp hκ)
  have hrange : (⊤ : Submodule Rhat Bhat) ≤
      LinearMap.range (Algebra.linearMap Rhat Bhat) ⊔
        maximalIdeal Rhat • (⊤ : Submodule Rhat Bhat) := by
    intro x _
    obtain ⟨aκ, haκ⟩ := hkg.surjective (residue Bhat x)
    obtain ⟨a, rfl⟩ := residue_surjective (R := Rhat) aκ
    have hmem : x - g a ∈ maximalIdeal Bhat := (residue_eq_zero_iff _).mp (by
      rw [map_sub, ← ResidueField.map_residue, ← haκ, sub_self])
    refine Submodule.mem_sup.mpr ⟨g a, LinearMap.mem_range.mpr ⟨a, rfl⟩, x - g a, ?_, by ring⟩
    rw [Ideal.smul_top_eq_map]
    change x - g a ∈ (maximalIdeal Rhat).map g
    rwa [hmax]
  exact LinearMap.range_eq_top.mp (eq_top_iff.mpr
    (Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp
      (moduleFinite_adicCompletion_of_formallyUnramified f hfu hft))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hrange))

/-- **Stacks Project, Tag 039H**, part (3). An unramified local homomorphism whose source has
separably closed residue field induces a surjection on completions. -/
@[stacks 039H "part (3)",
  ega "IV 17.4.4" "f'') k sep closed",
  sga "1 I 3.7" "unram ⇒ surj, κ sep cl", ega "IV 17.6.3" "partial"]
theorem surjective_adicCompletionMap_of_isSepClosed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (hfu : f.FormallyUnramified) (hft : f.EssFiniteType)
    [IsSepClosed (ResidueField A)] :
    Function.Surjective
      (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)) := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.FormallyUnramified A B := hfu
  have : Algebra.EssFiniteType A B := hft
  exact surjective_adicCompletionMap_of_bijective_residueFieldMap f hfu hft
    (by apply IsSepClosed.algebraMap_bijective)

/-- **Stacks Project, Tag 039H**, part (4). A local homomorphism of complete discrete valuation
rings is unramified exactly when it carries a uniformizer to a uniformizer, its residue field
extension is finite and separable, and it is essentially of finite type. -/
@[stacks 039H "part (4)"]
theorem unramified_iff_uniformizer_and_residueField
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] (ϖ : A) (hϖ : Irreducible ϖ) :
    letI := f.toAlgebra
    (Algebra.FormallyUnramified A B ∧ Algebra.EssFiniteType A B) ↔
      (Irreducible (f ϖ) ∧ Module.Finite (ResidueField A) (ResidueField B) ∧
        Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧ Algebra.EssFiniteType A B) := by
  let : Algebra A B := f.toAlgebra
  change (Algebra.FormallyUnramified A B ∧ Algebra.EssFiniteType A B) ↔ _
  constructor
  · rintro ⟨hfu, hft⟩
    have hirr : Irreducible (f ϖ) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer (f ϖ)).2 (by
        simpa only [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
          RingHom.algebraMap_toAlgebra] using
          (Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := B)).symm)
    exact ⟨hirr, inferInstance, inferInstance, hft⟩
  · rintro ⟨hirr, _, _, hft⟩
    have hmax : (maximalIdeal A).map f = maximalIdeal B := by
      simpa only [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] using
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer (f ϖ)).1 hirr).symm
    exact ⟨Algebra.FormallyUnramified.of_map_maximalIdeal hmax, hft⟩

end RingHom
