module

public import Mathlib.FieldTheory.ChevalleyWarning
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.BrauerGroupCField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupGaloisModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TorsionGaloisVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite field has cohomological dimension at most one

A finite field is a \(C_1\) field by the Chevalley–Warning theorem, so every finite extension of
it has trivial Brauer group (Stacks 03RC). By Stacks 03R8 part (2) the continuous cohomology of
its absolute Galois group with torsion coefficients vanishes in degrees `≥ 2`, and by Stacks
03QU this is the étale cohomology of `Spec` of the field. Hence `cd(Spec k) ≤ 1` for a finite
field `k`.

## Main results

* `IsCField.of_finite`: a finite field is a \(C_1\) field.
* `AlgebraicGeometry.isAddTorsion_etaleContinuousGModuleEquivalence_functor_obj`: the Galois
  module of a torsion abelian sheaf on the small étale site of the spectrum of a field is a
  torsion group.
* `AlgebraicGeometry.subsingleton_sheafH_spec_of_forall_brauer`: if every finite extension of a
  field `K` has trivial Brauer group, then `H^q_ét(Spec K, 𝓕) = 0` for every torsion abelian
  sheaf `𝓕` and every `q ≥ 2`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_one_of_finite`:
  `cd(Spec k) ≤ 1` for a finite field `k`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 03RC](https://stacks.math.columbia.edu/tag/03RC)
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A finite field is a \(C_1\) field.** A homogeneous polynomial of degree `d ≥ 1` in `n > d`
variables over a finite field of characteristic `p` vanishes at the origin, and by the
Chevalley–Warning theorem the number of its zeros is divisible by `p`; so it has a nonzero
zero. -/
theorem IsCField.of_finite (K : Type*) [Field K] [Finite K] : IsCField K 1 := by
  classical
  intro d n ⟨hd, hdn⟩ f hf
  have : Fintype K := Fintype.ofFinite K
  rw [pow_one] at hdn
  by_cases hf0 : f = 0
  · refine ⟨Pi.single ⟨0, by omega⟩ 1, fun h => ?_, by simp [hf0]⟩
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have htd : f.totalDegree < Fintype.card (Fin n) := by
    rwa [hf.totalDegree hf0, Fintype.card_fin]
  obtain ⟨p, hp⟩ := CharP.exists K
  have hprime : p.Prime :=
    (CharP.char_is_prime_or_zero K p).resolve_right (CharP.char_ne_zero_of_finite K p)
  have hdvd := char_dvd_card_solutions p htd
  by_contra hall
  push Not at hall
  have h0 : MvPolynomial.eval (0 : Fin n → K) f = 0 := by
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    exact hf.coeff_eq_zero (by simp; omega)
  have hcard : Fintype.card { x : Fin n → K // MvPolynomial.eval x f = 0 } = 1 :=
    Fintype.card_eq_one_iff.2 ⟨⟨0, h0⟩, fun ⟨x, hx⟩ => Subtype.ext
      (Classical.byContradiction fun hx0 => hall x hx0 hx)⟩
  rw [hcard] at hdvd
  exact hprime.one_lt.ne' (Nat.dvd_one.1 hdvd)

namespace AlgebraicGeometry

open Stacks.Torsion

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-- **The Galois module of a torsion sheaf is torsion.** For an abelian sheaf `𝓖` on the small
étale site of the spectrum of a field, the discrete Galois module attached to `𝓖` by the stalk
equivalence of Tag 04JQ has the stalk of `𝓖` as its underlying group; so it is a torsion group
when `𝓖` is a torsion sheaf. -/
theorem isAddTorsion_etaleContinuousGModuleEquivalence_functor_obj (B : BigEtaleSite.{u})
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K)))
    (G : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1})
    (hG : torsionSheafProperty (SmallEtale.topology B (Spec (.of K)) hK) G) :
    IsAddTorsion ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
      G).obj.obj.V := by
  let Γ := GeometricPoint.absoluteGaloisGroup sbar
  let e := continuousGModuleEquivContinuousGAddCommGrp.{u, u + 1} Γ
  let A := (abelianEtaleStalkEquivalence.{u, u + 1} B K hK sbar).functor.obj G
  let M := (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj G
  let φ : (ContinuousGAddCommGrp.forget Γ).obj (e.functor.obj M) ≅
      etaleStalk B (Spec (.of K)) hK sbar G.obj :=
    (ContinuousGAddCommGrp.forget Γ).mapIso (e.counitIso.app A) ≪≫
      (abelianEtaleStalkEquivalenceIso.{u, u + 1} B K hK sbar).app G
  intro m
  let m' : (ContinuousGAddCommGrp.forget Γ).obj (e.functor.obj M) := m
  obtain ⟨n, hn, h⟩ := SmallEtale.exists_nsmul_eq_zero_etaleStalk.{u, u + 1}
    B (Spec (.of K)) hK sbar G hG (φ.hom m')
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  have hinj : Function.Injective φ.hom := (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have : φ.hom (n • m') = φ.hom 0 := by rw [map_nsmul, h, map_zero]
  exact hinj this

/-- **Galois cohomological dimension one, read on the étale site** (Stacks 03R8 part (2) through
Stacks 03QU). If every finite extension of the field `K` has trivial Brauer group, then
`H^q_ét(Spec K, 𝓕) = 0` for every torsion abelian sheaf `𝓕` on the small étale site of `Spec K`
and every `q ≥ 2`. -/
theorem subsingleton_sheafH_spec_of_forall_brauer (K : Type u) [Field K]
    (hBr : ∀ (K' : Type u) [Field K'] [Algebra K K'] [Module.Finite K K']
      (y : BrauerGroup K'), y = 1)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : torsionSheafProperty (Spec (.of K)).smallEtaleTopology F) (q : ℕ) (hq : 2 ≤ q) :
    letI := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  let := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
  let B := BigEtaleSite.containing (Spec (.of K))
  have hK : B.Contains (Spec (.of K)) := BigEtaleSite.contains_containing _
  let sbar := GeometricPoint.ofAlgebraicClosure K
  refine (subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology B K hK sbar F q).2 ?_
  refine Stacks.GaloisCohomology.isZero_continuousGroupCohomology_of_isAddTorsion.{u, u + 1} _ _
    (fun L _ y => forall_forall_brauerGroup_residueField_eq_one K (sbar.hom default) hBr L y)
    _ ?_ q hq
  refine isAddTorsion_etaleContinuousGModuleEquivalence_functor_obj B K hK sbar _ ?_
  exact (SmallEtale.torsionSheafProperty_toEtaleSite_iff B (Spec (.of K)) hK F).2 hF

/-- **A finite field has cohomological dimension at most one.** Every finite extension of a
finite field `k` is a finite field, hence a \(C_1\) field (`IsCField.of_finite`), hence has
trivial Brauer group (Stacks 03RC); so the étale cohomology of `Spec k` with torsion coefficients
vanishes in degrees `≥ 2` (`AlgebraicGeometry.subsingleton_sheafH_spec_of_forall_brauer`). -/
@[sga "4½ Arcata 3.1.6" "special case"]
theorem Scheme.etaleCohomologicalDimension_spec_le_one_of_finite (k : Type u) [Field k]
    [Finite k] :
    letI := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of k))
    Scheme.etaleCohomologicalDimension (Spec (.of k)) ≤ 1 := by
  let := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of k))
  refine Scheme.etaleCohomologicalDimension_le _ 1 fun F hF q hq => ?_
  have hq2 : 2 ≤ q := by
    have : (1 : ℕ∞) < q := hq
    exact_mod_cast this
  refine subsingleton_sheafH_spec_of_forall_brauer k (fun K' _ _ _ y => ?_) F hF q hq2
  have : Finite K' := Module.finite_of_finite k
  exact brauerGroup_eq_one_of_isCField K' (IsCField.of_finite K') y

end AlgebraicGeometry

end
