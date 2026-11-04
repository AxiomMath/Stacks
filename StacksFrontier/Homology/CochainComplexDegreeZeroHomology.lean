module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The degree zero homology of a cochain complex indexed by `ℕ`

A cochain complex `K` indexed by `ℕ` has nothing in negative degrees, so no differential enters
degree zero and the degree zero homology is simply the kernel of the differential leaving it. For
complexes of abelian groups this file identifies the degree zero homology with the kernel subgroup,
composing `CochainComplex.isoHomologyπ₀`, which identifies the degree zero homology with the degree
zero cycles, and `AddCommGrpCat.kernelIsoKer`, which identifies a categorical kernel of abelian
groups with the kernel subgroup.

When the differential leaving degree zero vanishes the kernel is everything, and then the
degree zero homology is the degree zero term itself; that case needs no abelian groups and is
stated for an arbitrary category with zero morphisms.

## Main definitions

* `CochainComplex.homologyZeroIso` — `K.homology 0 ≅ K.X 0` when `K.d 0 1 = 0`, in any
  category with zero morphisms.
* `CochainComplex.homologyZeroIsoKernel` — `K.homology 0 ≅ ker (K.d 0 1)`, the kernel being the
  subgroup.
* `CochainComplex.homologyZeroIsoOfKerEq` — the same with the kernel replaced by any subgroup known
  to equal it.

## References

* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- **The degree zero homology of a cochain complex indexed by `ℕ` whose degree zero differential
vanishes is the degree zero term itself.** -/
def homologyZeroIso {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    (K : CochainComplex C ℕ) [K.HasHomology 0] (h : K.d 0 1 = 0) :
    K.homology 0 ≅ K.X 0 :=
  (isoHomologyπ₀ K).symm ≪≫ K.iCyclesIso 0 1 (by simp) h

/-- `CochainComplex.homologyZeroIso` is the canonical identification: it carries the class of a
degree zero cycle to that cycle. -/
theorem homologyπ_comp_homologyZeroIso_hom {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    (K : CochainComplex C ℕ) [K.HasHomology 0] (h : K.d 0 1 = 0) :
    K.homologyπ 0 ≫ (homologyZeroIso K h).hom = K.iCycles 0 := by
  simp [homologyZeroIso]

/-- **The degree zero homology of a cochain complex of abelian groups indexed by `ℕ` is the kernel
of its degree zero differential.** -/
def homologyZeroIsoKernel (K : CochainComplex AddCommGrpCat.{0} ℕ) :
    K.homology 0 ≅ AddCommGrpCat.of (AddMonoidHom.ker (K.d 0 1).hom) := by
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by simp
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  have hf : (K.sc' 0 0 1).f = 0 := K.shape 0 0 (by simp)
  exact K.homologyIsoSc' 0 0 1 hprev hnext ≪≫
    (ShortComplex.RightHomologyData.ofHasKernel _ hf).homologyIso ≪≫
    AddCommGrpCat.kernelIsoKer (K.d 0 1)

/-- `CochainComplex.homologyZeroIsoKernel` with the kernel presented as any subgroup equal to
it. -/
def homologyZeroIsoOfKerEq (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (H : AddSubgroup (K.X 0)) (hH : H = AddMonoidHom.ker (K.d 0 1).hom) :
    K.homology 0 ≅ AddCommGrpCat.of H :=
  homologyZeroIsoKernel K ≪≫
    eqToIso (congrArg (fun S : AddSubgroup (K.X 0) ↦ AddCommGrpCat.of S) hH.symm)

end CochainComplex

end
