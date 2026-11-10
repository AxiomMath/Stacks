module

public import Mathlib.LinearAlgebra.Contraction
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective trace as a contraction, and the étale trace pairing

The trace of an endomorphism of a finite projective module is the contraction of the tensor
representing it under the canonical isomorphism `Hom(P, P) ≅ P* ⊗ P`. This is the basis-free
description of `Stacks.Discriminant.finiteProjectiveTrace`, which is defined by computing on a
finite free module that `P` splits off.

That description identifies the trace pairing of a finite projective algebra with the
contraction trace used in the definition of the Dedekind complementary module. Combined with the
unit discriminant ideal of an étale algebra it also shows that the trace pairing of a finite
projective étale algebra is a perfect pairing.

## Main results

* `Stacks.Discriminant.finiteProjectiveTrace_eq_contract`: the projective trace is the
  contraction of the corresponding tensor.
* `Stacks.Discriminant.finiteProjectiveTraceForm_bijective_of_etale`: the trace pairing of a
  finite projective étale algebra is bijective onto the dual.

## Implementation notes

Surjectivity of the trace pairing is the unit discriminant ideal of an étale algebra,
`Stacks.Discriminant.algebraDiscriminantIdeal_eq_top_of_etale` together with
`Stacks.Discriminant.algebraDiscriminantIdeal_eq_top_iff_surjective`. Injectivity then comes for
free from symmetry of the pairing, since a finite projective module is separated by the
functionals coming from a finite free module it splits off.

## References

* [Stacks Project, Tag 0BJF](https://stacks.math.columbia.edu/tag/0BJF)
* [Stacks Project, Tag 0BW2](https://stacks.math.columbia.edu/tag/0BW2)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

/-- The trace of an endomorphism of a finite projective module, computed on a finite free module
that it splits off, is the contraction of the tensor representing it. -/
private theorem trace_split_eq_contract {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    {F : Type w} [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
    (p : F →ₗ[R] P) (i : P →ₗ[R] F)
    (hpi : p.comp i = LinearMap.id) (f : Module.End R P) :
    LinearMap.trace R F (i.comp (f.comp p)) =
      contractLeft R P ((dualTensorHomEquiv R P P).symm f) := by
  let τ : Module.Dual R P ⊗[R] P := (dualTensorHomEquiv R P P).symm f
  let τ' : Module.Dual R F ⊗[R] F := i.lTensor (Module.Dual R F) (p.dualMap.rTensor P τ)
  have h2 : dualTensorHom R F F τ' = i.comp (f.comp p) := by
    calc
      dualTensorHom R F F τ' =
          (i.compRight R ∘ₗ dualTensorHom R F P) ((p.dualMap.rTensor P) τ) :=
            congrArg (fun g : (Module.Dual R F ⊗[R] P) →ₗ[R] _ => g ((p.dualMap.rTensor P) τ))
              (dualTensorHom_comp_lTensor (R := R) (M := F) (N := P) (P := F) i)
      _ = (i.compRight R ∘ₗ p.lcomp R P ∘ₗ dualTensorHom R P P) τ :=
            congrArg (fun g : (Module.Dual R P ⊗[R] P) →ₗ[R] _ => (i.compRight R) (g τ))
              (dualTensorHom_comp_rTensor_dualMap (R := R) (M := F) (N := P) (P := P) p)
      _ = i.comp (f.comp p) := by
            ext x
            simp [τ, LinearMap.comp_apply]
  rw [LinearMap.trace_eq_contract']
  simp only [LinearMap.comp_apply]
  change contractLeft R F ((dualTensorHomEquiv R F F).symm (i.comp (f.comp p))) = _
  rw [← h2]
  change contractLeft R F ((dualTensorHomEquiv R F F).symm ((dualTensorHomEquiv R F F) τ')) = _
  rw [LinearEquiv.symm_apply_apply]
  have hc : ∀ t : Module.Dual R P ⊗[R] P,
      contractLeft R F (i.lTensor (Module.Dual R F) (p.dualMap.rTensor P t)) =
        contractLeft R P t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul φ x =>
      have hx : p (i x) = x := by simpa using LinearMap.congr_fun hpi x
      simp [contractLeft_apply, hx]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact hc τ

/-- The trace of an endomorphism of a finite projective module is the contraction of the tensor
representing it under `Hom(P, P) ≅ P* ⊗ P`. -/
theorem finiteProjectiveTrace_eq_contract {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    finiteProjectiveTrace R P f =
      contractLeft R P ((dualTensorHomEquiv R P P).symm f) := by
  classical
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  rw [finiteProjectiveTrace_eq_trace_of_split R P (Fin n → R) p i hpi f]
  exact trace_split_eq_contract p i hpi f

/-- A symmetric surjective map from a finite projective module to its dual is injective: the
functionals coming from a finite free module the module splits off separate its points. -/
private theorem linearMap_injective_of_surjective_symmetric {R : Type u} [CommRing R]
    {A : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    (T : A →ₗ[R] Module.Dual R A) (hsurj : Function.Surjective T)
    (hsymm : ∀ x y, T x y = T y x) : Function.Injective T := by
  obtain ⟨n, p, i, _, hi, _⟩ := Module.Finite.exists_comp_eq_id_of_projective R A
  intro x y hxy
  apply hi
  ext j
  have hφ : ((LinearMap.proj j).comp i) (x - y) = 0 := by
    obtain ⟨w, hw⟩ := hsurj ((LinearMap.proj j).comp i)
    calc
      ((LinearMap.proj j).comp i) (x - y) = T w (x - y) := by rw [hw]
      _ = T (x - y) w := hsymm w (x - y)
      _ = 0 := by rw [map_sub, hxy, sub_self, LinearMap.zero_apply]
  simpa only [LinearMap.comp_apply, LinearMap.proj_apply, map_sub, sub_eq_zero] using hφ

/-- The trace pairing of a finite projective étale algebra is a bijection onto the linear
dual. -/
@[sga "1 I 4.10" "partial"]
theorem finiteProjectiveTraceForm_bijective_of_etale {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Module.Projective R S] [Algebra.Etale R S] :
    Function.Bijective (finiteProjectiveTraceForm R S) := by
  have hsurj : Function.Surjective (finiteProjectiveTraceForm R S) :=
    (algebraDiscriminantIdeal_eq_top_iff_surjective R S).mp
      (algebraDiscriminantIdeal_eq_top_of_etale R S inferInstance)
  exact ⟨linearMap_injective_of_surjective_symmetric _ hsurj
    (finiteProjectiveTraceForm_apply_symm R S), hsurj⟩

end Stacks.Discriminant

end
