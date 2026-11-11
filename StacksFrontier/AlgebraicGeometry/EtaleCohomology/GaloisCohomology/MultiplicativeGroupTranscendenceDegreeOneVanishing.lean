module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupGaloisModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupTranscendenceDegreeOne
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the étale cohomology of `𝐆_m` over a transcendence-degree-one extension

Let `k` be an algebraically closed field and `K/k` a field extension of transcendence degree
one. Then `H^q_étale(Spec K, 𝐆_m) = 0` for every `q ≥ 1` (Stacks 03RG).

The source's proof has two steps. By Stacks 03QU and Stacks 03R8 it suffices that every finite
extension of `K` has trivial Brauer group; that criterion is
`AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer`, which assembles
part (1) of Stacks 03R8 in every degree with part (3) of Stacks 03QU at `𝐆_m`. The Brauer premise
is `Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_of_trdeg_eq_one`: a finite
extension of `K` again has transcendence degree one over `k`, hence is a \(C_1\) field, hence has
trivial Brauer group (Stacks 03RF, Stacks 03RC).

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one`:
  **Stacks 03RG**.
* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_isAlgebraic`: the same
  vanishing at every algebraic extension of `K`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_functionField`: the same
  vanishing at the function field of a curve over `k`.

## Implementation notes

Abelian sheaves on the small étale site of a `Scheme.{u}` have coefficients in
`AddCommGrpCat.{u + 1}` and cohomology is `CategoryTheory.Sheaf.H.{u + 1, u + 1}`, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing`.

## References

* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG)
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Stacks Project, Tag 03RG.** Let `k` be an algebraically closed field and `K/k` a field
extension of transcendence degree one. Then

`H^q_étale(Spec K, 𝐆_m) = 0` for every `q ≥ 1`.

The criterion of Stacks 03R8 read through Stacks 03QU,
`AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer`, reduces this to
the triviality of the Brauer group of every finite extension `K'/K`; such a `K'` has
transcendence degree one over `k`, so `Br(K') = 0` by
`Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_of_trdeg_eq_one`. -/
@[stacks 03RG, sga "4½ Arcata 3.1.6" "clause i), special case", sga "4½ Arcata 3.2.4"]
theorem subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one (k : Type u) [Field k]
    [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K] (hK : Algebra.trdeg k K = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q) := by
  refine subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer K (fun K' _ _ _ y ↦ ?_) q hq
  let _ : Algebra k K' := ((algebraMap K K').comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K K' := .of_algebraMap_eq' rfl
  exact brauerGroup_eq_one_of_module_finite_of_trdeg_eq_one k K hK K' y

/-- **Stacks 03RG at every algebraic extension of a transcendence-degree-one extension.** Let `k`
be an algebraically closed field and `K/k` an extension of transcendence degree one. Then for
every algebraic extension `L` of `K`, `H^q_étale(Spec L, 𝐆_m) = 0` for every `q ≥ 1`: `L` again
has transcendence degree one over `k`. -/
theorem subsingleton_sheafH_multiplicativeSheaf_spec_of_isAlgebraic (k : Type u) [Field k]
    [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K] (hK : Algebra.trdeg k K = 1)
    (L : Type u) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q) := by
  let _ : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K L := .of_algebraMap_eq' rfl
  exact subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one k L
    (trdeg_eq_one_of_isAlgebraic k K hK L) q hq

/-- **Stacks 03RG at the function field of a curve.** Let `X` be a curve over an algebraically
closed field `k`. Then `H^q_étale(Spec k(X), 𝐆_m) = 0` for every `q ≥ 1`. The Brauer premise of
the criterion is `Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_functionField`. -/
@[sga "4 IX 4.4" "(4.4.1) for Spec R(X)", sga "4½ Arcata 3.2.4" "K = k(X)"]
theorem subsingleton_sheafH_multiplicativeSheaf_spec_functionField (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField)) q) :=
  subsingleton_sheafH_multiplicativeSheaf_of_forall_brauer ↥X.functionField
    (fun K' _ _ _ y ↦ brauerGroup_eq_one_of_module_finite_functionField k f K' y) q hq

/-- **Stacks Project, Tag 03RG**, under its earlier name: an alias of
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one`. Let `k`
be an algebraically closed field and `K/k` a field extension of transcendence degree one. Then
`H^q_étale(Spec K, 𝐆_m) = 0` for every `q ≥ 1`. -/
@[stacks 03RG "vanishing of the positive-degree étale cohomology of 𝐆_m over a
transcendence-degree-one extension of an algebraically closed field, proved from Tag 03R8 and
Tag 03QU with no hypothesis beyond the tag's"]
alias subsingleton_sheafH_multiplicativeSheaf_of_trdeg_eq_one :=
  subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one

end Stacks.EtaleCohomology

end
