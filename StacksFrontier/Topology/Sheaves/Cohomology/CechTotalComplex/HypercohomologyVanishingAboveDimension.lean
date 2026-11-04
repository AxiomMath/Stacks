module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCech
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransfer
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Vanishing of hypercohomology above the dimension of a Noetherian space

Let `X` be a Noetherian topological space of dimension at most `d` with a sheaf `𝒪_X` of
commutative rings, and let `ℱ` be a sheaf of `𝒪_X`-modules. The hypercohomology `Hⁿ(X, ℱ[0])` is
the cohomology of the underlying abelian sheaf ([Stacks, Tag 01F1]), which vanishes for `n > d`
by Grothendieck's theorem ([Stacks, Tag 02UZ]). When Čech cohomology computes the cohomology of
`ℱ` placed in degree `a` and in degree `0`, the two hypercohomologies are identified up to the
shift by `a`, so `Hⁿ(X, ℱ[-a])` vanishes for `n > d + a`.

## Main results

* `Stacks.Cech.Hypercohomology.isZero_hypercohomology_singlePlus_zero_of_lt`: `Hⁿ(X, ℱ[0]) = 0`
  for `n > d`.
* `Stacks.Cech.Hypercohomology.isZero_hypercohomology_singlePlus_of_lt_sub`: `Hⁿ(X, ℱ[-a]) = 0`
  for `n - a > d`.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

namespace Stacks.Cech.Hypercohomology

open scoped Stacks.StandardDerivedModel

variable {X : TopCat.{u}} [NoetherianSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (F : SheafOfModules.{u} (ringSheaf O))
  {d : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

include hdim in
/-- **Grothendieck's vanishing theorem for hypercohomology of a module placed in degree zero**
([Stacks, Tags 02UZ, 01F1]): on a Noetherian space of dimension at most `d`,
`Hⁿ(X, ℱ[0]) = 0` for `n > d`. -/
theorem isZero_hypercohomology_singlePlus_zero_of_lt {n : ℕ} (hn : d < n) :
    IsZero (hypercohomology O (singlePlus O F 0) n) := by
  have : Subsingleton ((Sheaf.functorH (Opens.grothendieckTopology X) n).obj
      ((SheafOfModules.toSheaf (ringSheaf O)).obj F)) :=
    Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le hdim hn _
  exact ModuleCat.isZero_iff_subsingleton.mpr <| AddCommGrpCat.subsingleton_of_isZero <|
    ((AddCommGrpCat.isZero_of_subsingleton _).of_iso
      ((Stacks.Cohomology.TopDegree.functorHIsoSectionsRightDerived X n).app _).symm).of_iso
      ((rightDerivedToSheafIso O n).app F).symm

include hdim in
/-- **Grothendieck's vanishing theorem for a module placed in degree `a`**: when Čech cohomology
computes the cohomology of `ℱ[-a]` and of `ℱ[0]`, on a Noetherian space of dimension at most `d`,
`Hⁿ(X, ℱ[-a]) = 0` for `n - a > d`. -/
theorem isZero_hypercohomology_singlePlus_of_lt_sub (a : ℤ)
    (hF : CechComputes O (singlePlus O F a)) (hF₀ : CechComputes O (singlePlus O F 0)) {n : ℤ}
    (hn : (d : ℤ) < n - a) : IsZero (hypercohomology O (singlePlus O F a) n) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = (p : ℤ) + a := ⟨(n - a).toNat, by omega⟩
  have : Subsingleton (hypercohomology O (singlePlus O F 0) ((p : ℤ) + 0)) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_hypercohomology_singlePlus_zero_of_lt O F hdim (n := p) (by lia))
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y =>
    (cechTransferEquiv a 0 (Iso.refl _) hF hF₀ p).injective (Subsingleton.elim _ _)⟩

end Stacks.Cech.Hypercohomology

end
