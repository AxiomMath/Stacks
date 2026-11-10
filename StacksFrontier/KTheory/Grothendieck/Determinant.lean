module

public import Mathlib.RingTheory.PicardGroup
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact
public import StacksFrontier.KTheory.Grothendieck.Defs

/-!
# The determinant map from `K₀` to the Picard group

Let `R` be a commutative ring. The determinant line of a finite projective module is invertible,
and it is multiplicative in short exact sequences, so taking determinants respects the defining
relations of `K₀(R)` and descends to a homomorphism `K₀(R) → Pic(R)`. On the class of a module of
constant rank `n` it is the class of the `n`-th exterior power.

## Main results

* `K0.exists_determinant_hom`: the determinant homomorphism `K₀(R) → Pic(R)` exists and is
  computed on classes of modules of constant rank by the top exterior power.

## Implementation notes

The Picard group is written multiplicatively, so the homomorphism lands in
`Additive (CommRing.Pic R)`. The statement is existential because the homomorphism is
constructed from the determinant line, whose formation involves the rank decomposition of the
module; the characterization on classes of constant-rank modules determines it.

## References

* [Stacks Project, Tag 0AFX](https://stacks.math.columbia.edu/tag/0AFX)
-/

section

universe u v

open scoped BigOperators

open ProjectiveDeterminant

private lemma rankIdempotent_eq_of_rank
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n k : ℕ)
    (h : Module.rankAtStalk M = Function.const (PrimeSpectrum R) n) :
    rankIdempotent (R := R) (M := M) k = if k = n then 1 else 0 := by
  have key (j : ℕ) (e : R) (he : IsIdempotentElem e)
      (hj : rankLocus (R := R) M j = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))) :
      rankIdempotent (R := R) (M := M) j = e :=
    ((Classical.choose_spec
      (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
        (rankLocus_isClopen (R := R) (M := M) j))).2 e ⟨he, hj⟩).symm
  split_ifs with hk
  · subst k
    refine key _ _ IsIdempotentElem.one ?_
    ext p
    simp [rankLocus, congrFun h p]
  · refine key _ _ IsIdempotentElem.zero ?_
    ext p
    simp [rankLocus, congrFun h p, Ne.symm hk]

private lemma submodule_eq_exteriorPower
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ)
    (h : Module.rankAtStalk M = Function.const (PrimeSpectrum R) n) :
    submodule (R := R) (M := M) = (⋀[R]^n M) := by
  rw [submodule]
  apply le_antisymm
  · refine iSup_le fun k => ?_
    rw [component, rankIdempotent_eq_of_rank n k h]
    split_ifs with hk
    · subst k
      simp
    · simp
  · refine le_trans ?_ (le_iSup (fun k : ℕ => component (R := R) (M := M) k) n)
    rw [component, rankIdempotent_eq_of_rank n n h]
    simp

@[sga "6 X 6.2.7" "special case"]
private noncomputable def detModuleEquivDirectSum
    {R : Type u} [CommRing R] (M N : FGProj R) :
    TensorProduct R (module (R := R) (M := M.carrier))
      (module (R := R) (M := N.carrier)) ≃ₗ[R]
        module (R := R) (M := (M.directSum N).carrier) := by
  let eM := LinearEquiv.ofEq _ _
    (ProjectiveDeterminant.determinant_submodule_eq_annihilator R M.carrier)
  let eN := LinearEquiv.ofEq _ _
    (ProjectiveDeterminant.determinant_submodule_eq_annihilator R N.carrier)
  let eMN := LinearEquiv.ofEq _ _
    (ProjectiveDeterminant.determinant_submodule_eq_annihilator R (M.directSum N).carrier)
  exact (TensorProduct.congr eM eN).trans
    ((ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact (LinearMap.inl R _ _)
      (LinearMap.snd R _ _) LinearMap.inl_injective Function.Exact.inl_snd
      LinearMap.snd_surjective).1.trans eMN.symm)

private noncomputable def detClass {R : Type u} [CommRing R] (M : FGProj R) :
    Additive (CommRing.Pic R) := by
  letI := ProjectiveDeterminant.invertible (R := R) (M := M.carrier)
  exact Additive.ofMul (CommRing.Pic.mk R (module (R := R) (M := M.carrier)))

@[sga "6 X 6.2.7" "partial"]
private lemma detClass_directSum {R : Type u} [CommRing R] (M N : FGProj R) :
    detClass (M.directSum N) = detClass M + detClass N := by
  let := ProjectiveDeterminant.invertible (R := R) (M := M.carrier)
  let := ProjectiveDeterminant.invertible (R := R) (M := N.carrier)
  let := ProjectiveDeterminant.invertible (R := R) (M := (M.directSum N).carrier)
  change CommRing.Pic.mk R (module (R := R) (M := (M.directSum N).carrier)) =
    CommRing.Pic.mk R (module (R := R) (M := M.carrier)) *
      CommRing.Pic.mk R (module (R := R) (M := N.carrier))
  rw [← CommRing.Pic.mk_tensor]
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨(detModuleEquivDirectSum M N).symm⟩

/-- An isomorphism from the determinant line of `M` to an invertible module `N` identifies the
class of `M` with the class of `N`. -/
private lemma detClass_eq_of_linearEquiv {R : Type u} [CommRing R] (M : FGProj R) (N : Type u)
    [AddCommGroup N] [Module R N] [Module.Invertible R N]
    (e : module (R := R) (M := M.carrier) ≃ₗ[R] N) :
    detClass M = Additive.ofMul (CommRing.Pic.mk R N) := by
  let := ProjectiveDeterminant.invertible (R := R) (M := M.carrier)
  exact Additive.toMul.injective (CommRing.Pic.mk_eq_mk_iff.mpr ⟨e⟩)

private lemma detClass_eq_of_iso {R : Type u} [CommRing R] (M N : FGProj R)
    (e : M.carrier ≃ₗ[R] N.carrier) : detClass M = detClass N :=
  let := ProjectiveDeterminant.invertible (R := R) (M := N.carrier)
  detClass_eq_of_linearEquiv M _ (ProjectiveDeterminant.mapEquiv e)

private noncomputable def determinantHom {R : Type u} [CommRing R] :
    K0 R →+ Additive (CommRing.Pic R) := by
  let F : FreeAbelianGroup (FGProj R) →+ Additive (CommRing.Pic R) :=
    FreeAbelianGroup.lift detClass
  refine QuotientAddGroup.lift (K0.rels R) F ?_
  intro x hx
  refine AddSubgroup.closure_induction (p := fun x _ => F x = 0) ?_ ?_ ?_ ?_ hx
  · rintro y (⟨M, N, rfl⟩ | ⟨M, N, ⟨e⟩, rfl⟩)
    · simp only [F, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [detClass_directSum]
      simp
    · simp only [F, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [detClass_eq_of_iso M N e]
      simp
  · exact map_zero F
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro a _ ha
    rw [map_neg, ha, neg_zero]

private lemma determinantHom_mk {R : Type u} [CommRing R] (M : FGProj R) :
    determinantHom (R := R) (K0.mk M) = detClass M :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **Stacks 0AFX.** The determinant gives a homomorphism from `K₀(R)` to the Picard group.
For a finite locally free module of constant rank `n`, it sends its class to the class of its
`n`th exterior power. -/
@[stacks 0AFX, sga "6 X 5.1" "affine case"]
public theorem K0.exists_determinant_hom (R : Type u) [CommRing R] :
    ∃ det : K0 R →+ Additive (CommRing.Pic R),
      ∀ (M : FGProj R) (n : ℕ),
        Module.rankAtStalk M.carrier = Function.const (PrimeSpectrum R) n →
          ∃ h : Module.Invertible R (⋀[R]^n M.carrier),
            det (K0.mk M) =
              Additive.ofMul (@CommRing.Pic.mk R (⋀[R]^n M.carrier) inferInstance
                inferInstance inferInstance h)
    := by
  refine ⟨determinantHom, fun M n hn => ?_⟩
  have e : module (R := R) (M := M.carrier) ≃ₗ[R] ↥(⋀[R]^n M.carrier) :=
    LinearEquiv.ofEq _ _ (submodule_eq_exteriorPower n hn)
  let := ProjectiveDeterminant.invertible (R := R) (M := M.carrier)
  let h : Module.Invertible R (⋀[R]^n M.carrier) := Module.Invertible.congr e
  refine ⟨h, ?_⟩
  rw [determinantHom_mk]
  exact detClass_eq_of_linearEquiv M _ e

end
